package rpi

import java.nio.file.{Files, Paths}
import java.util.concurrent.atomic.AtomicInteger

import fastparse.core.Parsed.Success
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast._
import viper.silver.parser.{FastParser, PProgram, Resolver, Translator}

import scala.io.Source
import scala.util.Properties


object Inference {
  /**
    * Returns he file to be parsed.
    *
    * @return The file to be parsed.
    */
  def file: String = _file.get

  /**
    * Returns the path to the z3 executable.
    *
    * @return The path to the z3 executable.
    */
  def z3: String = _z3
    .orElse(Properties.envOrNone("Z3_EXE"))
    .getOrElse {
      val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")
      if (isWindows) "z3.exe" else "z3"
    }

  /**
    * The file to be parsed.
    */
  private var _file: Option[String] = None

  /**
    * The path to the z3 executable.
    */
  private var _z3: Option[String] = None

  /**
    * The entry point of the inference.
    *
    * @param args The command line arguments.
    */
  def main(args: Array[String]): Unit = {
    // process arguments
    processArgs(args)

    // run inference
    val program = parse(file).get
    val inference = new Inference(program)
    inference.start()
    val annotated = inference.infer()
    inference.stop()

    println("----- annotated program -----")
    println(annotated)
  }

  /**
    * Process the given arguments. The first argument is expected to be the file to be parsed. After that a sequence of
    * of options may follow.
    *
    * @param args The arguments.
    */
  private def processArgs(args: Seq[String]): Unit = {
    // get file
    assert(args.nonEmpty, "no file specified.")
    _file = Some(args.head)
    // process options
    processOptions(args.tail)
  }

  /**
    * Processes the sequence of options represented by the given arguments.
    *
    * @param args The arguments.
    */
  private def processOptions(args: Seq[String]): Unit = args match {
    case "-z3" +: value +: rest => _z3 = Some(value); processOptions(rest)
    case _ +: rest => processOptions(rest) // ignore unknown option
    case Nil => // we are done
  }

  /**
    * Parses the given file.
    *
    * @param file The file to parse.
    * @return The parsed program.
    */
  private def parse(file: String): Option[Program] = {
    // read input
    val path = Paths.get(file)
    val input = Source.fromInputStream(Files.newInputStream(path)).mkString
    // parse program
    val program = FastParser.parse(input, path, None) match {
      case Success(program: PProgram, _) if program.errors.isEmpty =>
        program.initProperties()
        Some(program)
      case _ => None
    }
    // resolve and translate program
    program
      .flatMap(Resolver(_).run)
      .flatMap(Translator(_).translate)
  }
}

class Inference(val program: Program) {
  /**
    * The teacher providing the examples.
    */
  private val teacher: Teacher = new Teacher(this)

  /**
    * The learner used synthesizing hypotheses.
    */
  private val learner: Learner = new Learner(this)

  /**
    * The sequence of atomic predicates.
    */
  lazy val atoms: Seq[Exp] = program
    .deepCollect { case While(cond, _, _) => cond }
    .distinct

  /**
    * The program annotated with predicates in all the places where some specification should be inferred.
    */
  lazy val labelled: Program = {
    val id = new AtomicInteger()
    program.transform({
      case method: Method =>
        val args = method.formalArgs.map(v => LocalVar(v.name, v.typ)())
        val pres = method.pres :+ PredicateAccessPredicate(PredicateAccess(args, s"P_${method.name}")(), FullPerm()())()
        val posts = method.posts :+ PredicateAccessPredicate(PredicateAccess(args, s"Q_${method.name}")(), FullPerm()())()
        method.copy(pres = pres, posts = posts)(method.pos, method.info, method.errT)
      case loop: While =>
        val invs = loop.invs :+ PredicateAccessPredicate(PredicateAccess(Seq.empty, s"I_${id.getAndIncrement()}")(), FullPerm()())()
        loop.copy(invs = invs)(loop.pos, loop.info, loop.errT)
    }, Traverse.TopDown)
  }

  lazy val predicates: Seq[PredicateAccess] = labelled.deepCollect {
    case p: PredicateAccess => p
  }

  /**
    * TODO: Framing
    */
  lazy val triples: Seq[Triple] = {
    val methods = labelled.methods.map(m => m.name -> m).toMap

    def collectTriples(triples: Seq[Triple], pres: Seq[Exp], before: Seq[Stmt], stmt: Stmt): (Seq[Triple], Seq[Exp], Seq[Stmt]) = stmt match {
      case Seqn(stmts, _) =>
        stmts.foldLeft((triples, pres, before)) { case ((ts, ps, bs), s) => collectTriples(ts, ps, bs, s) }
      case While(cond, invs, body) =>
        val t1 = Triple(pres, invs, Seqn(before, Seq.empty)())
        val (ts1, ps1, bs1) = collectTriples(triples :+ t1, invs :+ cond, Seq.empty, body)
        val t2 = Triple(ps1, invs, Seqn(bs1, Seq.empty)())
        (ts1 :+ t2, invs :+ Not(cond)(), Seq.empty)
      case MethodCall(name, args, _) =>
        val method = methods(name)
        val ps1 = method.pres.init :+ PredicateAccessPredicate(PredicateAccess(args, s"P_${method.name}")(), FullPerm()())()
        val ps2 = method.posts.init :+ PredicateAccessPredicate(PredicateAccess(args, s"Q_${method.name}")(), FullPerm()())()
        val part = Triple(pres, ps1, Seqn(before, Seq.empty)())
        (triples :+ part, ps2, Seq.empty)
      case _ =>
        (triples, pres, before :+ stmt)
    }

    labelled.methods.flatMap {
      case Method(name, args, _, pres, posts, Some(body)) =>
        val (ts, ps, bs) = collectTriples(Seq.empty, pres, Seq.empty, body)
        val t = Triple(ps, posts, Seqn(bs, Seq.empty)())
        ts :+ t
      case _ => Seq.empty
    }
  }

  /**
    * Starts the inference and all of its subcomponents.
    */
  def start(): Unit = {
    teacher.start()
    learner.start()
  }

  /**
    * Stops the inference and all of its subcomponents.
    */
  def stop(): Unit = {
    teacher.stop()
    learner.stop()
  }

  def infer(): Program = {
    var hypothesis: Seq[Predicate] = learner.initial()

    for (i <- 0 until 4) {
      println(s"----- round $i -----")
      val examples = teacher.check(hypothesis)
      learner.addExamples(examples)
      hypothesis = learner.hypothesis()
    }

    // annotate program with inferred specifications
    val map = hypothesis.map(pred => pred.name -> pred).toMap
    annotated(map)
  }

  private def annotated(hypothesis: Map[String, Predicate]): Program = {
    val predicates = labelled.predicates ++ hypothesis.values
    val methods = labelled.methods.map { method =>
      val body = method.body match {
        case Some(seqn) =>
          val unfold = method.pres.collectFirst { case p: PredicateAccessPredicate => Unfold(p)() }.get
          val fold = method.posts.collectFirst { case p: PredicateAccessPredicate => Fold(p)() }.get
          val x = seqn.transform({
            case call@MethodCall(name, args, _) =>
              val mp = Fold(PredicateAccessPredicate(PredicateAccess(args, hypothesis(s"P_$name").name)(), FullPerm()())())()
              val mq = Unfold(PredicateAccessPredicate(PredicateAccess(args, hypothesis(s"Q_$name").name)(), FullPerm()())())()
              Seqn(Seq(mp, call, mq), Seq.empty)()
          }, Traverse.BottomUp)
          val stmts = unfold +: x.ss :+ fold
          Some(Seqn(stmts, seqn.scopedDecls)())
        case none => none
      }
      method.copy(body = body)(method.pos, method.info, method.errT)
    }
    labelled.copy(predicates = predicates, methods = methods)(NoPosition, NoInfo, NoTrafos)
  }
}

case class Triple(pres: Seq[Exp], posts: Seq[Exp], body: Seqn) {
  override def toString: String = {
    val p = pres.map(_.toString()).reduceOption((x, y) => s"$x && $y").getOrElse("true")
    val q = posts.map(_.toString()).reduceOption((x, y) => s"$x && $y").getOrElse("true")
    val s = body.ss.map(_.toString()).reduceOption((x, y) => s"$x; $y").getOrElse("skip")
    s"{$p} $s {$q}"
  }
}