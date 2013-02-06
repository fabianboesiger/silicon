package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter,
    HeapMerger, PermissionChunk}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.reporting.TraceView
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{DirectFieldChunk, DirectPredicateChunk, TypeConverter, DirectChunk}
import reporting.{DefaultContext, Producing, ImplBranching, Bookkeeper}

trait DefaultProducer[
                      ST <: Store[ST],
                      H <: Heap[H],
											PC <: PathConditions[PC],
                      S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Producer[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV] with HasLocalState
		{ this: Logging with Evaluator[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV]
                    with Consumer[PermissionsTuple, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
									  with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]

	protected val decider: Decider[PermissionsTuple, ST, H, PC, S, C]
	import decider.{fresh, assume}
	
	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val heapMerger: HeapMerger[H]
	import heapMerger.merge
	
	protected val typeConverter: TypeConverter
	import typeConverter.toSort
	
  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshPermVar

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config
	
	private var snapshotCacheFrames: Stack[Map[Term, (Term, Term)]] = Stack()
	private var snapshotCache: Map[Term, (Term, Term)] = Map()

	def produce(σ: S,
              sf: Sort => Term,
              p: PermissionsTuple,
              φ: ast.Expression,
              pve: PartialVerificationError,
              c: C,
              tv: TV)
			       (Q: (S, C) => VerificationResult)
             : VerificationResult =

    produce2(σ, sf, p, φ, pve, c, tv)((h, c1) => {
      val (mh, mts) = merge(Ø, h)
      assume(mts, c1)
      Q(σ \ mh, c1)})

  def produces(σ: S,
               sf: Sort => Term,
               p: PermissionsTuple,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, C) => VerificationResult)
              : VerificationResult =

    if (φs.isEmpty)
      Q(σ, c)
    else
      produce(σ, sf, p, φs.head, pvef(φs.head), c, tv)((σ1, c1) =>
        produces(σ1, sf, p, φs.tail, pvef, c1, tv)(Q))

  private def produce2(σ: S,
                       sf: Sort => Term,
                       p: PermissionsTuple,
                       φ: ast.Expression,
                       pve: PartialVerificationError,
                       c: C,
                       tv: TV)
                       (Q: (H, C) => VerificationResult)
                      : VerificationResult = {

    val tv1 = tv.stepInto(c, Producing[ST, H, S](σ, p, φ))
       
    internalProduce(σ, sf, p, φ, pve, c, tv1)((h, c1) => {
      tv1.currentStep.σPost = σ \ h
      Q(h, c1)
    })
  }

	private def internalProduce(σ: S,
                              sf: Sort => Term,
                              p: PermissionsTuple,
                              φ: ast.Expression,
                              pve: PartialVerificationError,
                              c: C,
                              tv: TV)
			                       (Q: (H, C) => VerificationResult)
                             : VerificationResult = {

		logger.debug("\nPRODUCE " + φ.toString)
		logger.debug(stateFormatter.format(σ))

		val produced = φ match {
      /* And <: BooleanExpr */
      case ast.BinaryOp(_: ast.And, a0, a1) /* if !φ.isPure */ =>
        val s0 = fresh(sorts.Snap)
        val s1 = fresh(sorts.Snap)
        val tSnapEq = SnapEq(sf(sorts.Snap), Combine(s0, s1))

        val sf0 = (sort: Sort) => s0.convert(sort)
        val sf1 = (sort: Sort) => s1.convert(sort)

				assume(tSnapEq, c)
        produce2(σ, sf0, p, a0, pve, c, tv)((h1, c1) =>
          produce2(σ \ h1, sf1, p, a1, pve, c1, tv)((h2, c2) =>
          Q(h2, c2)))

			/* Implies <: BooleanExpr */
      case ast.BinaryOp(_: ast.Implies, e0, a0) /* if !φ.isPure */ =>
				eval(σ, e0, pve, c, tv)((t0, c1) =>
					branch(t0, c1, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => produce2(σ, sf, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(σ.h, c2)))

      case ast.Access(fa @ ast.FieldLocation(eRcvr, field), gain) =>
        producePermissions[DirectFieldChunk](σ, sf, p, fa, gain, DirectFieldChunk, toSort(field.dataType), pve, c, tv)((h, ch, c1) =>
          Q(h, c1))

      case ast.Access(pa @ ast.PredicateLocation(eRcvr, field), gain) =>
        val dpc =
          (rcvr: Term, id: String, snap: Term, p: PermissionsTuple) =>
            DirectPredicateChunk(rcvr, id, snap, p)

        producePermissions[DirectPredicateChunk](σ, sf, p, pa, gain, dpc, sorts.Snap, pve, c, tv)((h, _, c1) =>
          Q(h, c1))

      case qe @ ast.Quantified(
                  ast.Exists(),
                  qvar,
                  ast.BinaryOp(
                    _: ast.And,
                    rdStarConstraints,
                    pe @ ast.FieldAccessPredicate(
                            ast.FieldLocation(eRcvr, field),
                            _)))
            if toSort(qvar.dataType) == sorts.Perms =>

        val witness = qvar
        val (tWitness, _) = freshPermVar(witness.name)
        val σ1 = σ \+ (witness, tWitness)
        eval(σ1, rdStarConstraints, pve, c, tv)((tRdStarConstraints, c1) => {
          assume(tRdStarConstraints, c1)
          produce2(σ1, sf, p, pe, pve, c1, tv)((h1, c2) =>
            Q(h1, c2))})

			/* Any regular expressions, i.e. boolean and arithmetic. */
			case _ =>
				eval(σ, φ, pve, c, tv)((t, c1) => {
					assume(t, c1)
          Q(σ.h, c1)})
		}

		produced
	}

  /* TODO: Replace parameters sf and sort by s: Sort and apply sf(sort) prior
   *       to calling the method.
   */
  private def producePermissions[CH <: PermissionChunk]
                                (σ: S,
                                 sf: Sort => Term,
                                 p: PermissionsTuple,
                                 memloc: ast.MemoryLocation,
                                 gain: ast.Expression,
                                 chConstructor: (Term, String, Term, PermissionsTuple) => CH,
                                 sort: Sort,
                                 pve: PartialVerificationError,
                                 c: C,
                                 tv: TV)
                                (Q: (H, CH, C) => VerificationResult)
                                : VerificationResult = {

    val ast.MemoryLocation(eRcvr, id) = memloc

    eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) => {
      assume(tRcvr !== Null(), c1)
      evalp(σ, gain, pve, c1, tv)((pGain, c3) =>
        decider.isValidFraction(pGain, gain) match {
          case None =>
            val s = sf(sort)
            val (pNettoGain: PermissionsTuple, tFr: Set[Term]) =
                (pGain * p, Set[Term](True()))
            val ch = chConstructor(tRcvr, id, s, pNettoGain)
            val (mh, mts) = merge(σ.h, H(ch :: Nil))
            assume(mts ++ tFr, c3)
            Q(mh, ch, c3)

          case Some(reason) =>
            Failure[C, ST, H, S, TV](pve dueTo reason, c3, tv)})})
  }
	
	override def pushLocalState() {
		snapshotCacheFrames = snapshotCacheFrames.push(snapshotCache)
		super.pushLocalState()
	}
	
	override def popLocalState() {
		snapshotCache = snapshotCacheFrames.top
		snapshotCacheFrames = snapshotCacheFrames.pop
		super.popLocalState()
	}
}