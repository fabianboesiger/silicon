// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silver.cfg.silver.SilverCfg
import viper.silicon.common.Mergeable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.rules.{stateConsolidator}
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.{And, Equals, Implies, Ite, NoPerm, Term, Var}
import viper.silicon.supporters.functions.{FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.{Map, Stack}

import scala.collection.mutable.{HashMap, Queue}
import viper.silicon.verifier.Verifier
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverLoopHeadBlock}

final case class State(g: Store = Store(),
                       h: Heap = Heap(),
                       oldHeaps: OldHeaps = Map.empty, // TODO: Merge

                       parallelizeBranches: Boolean = false,

                       recordVisited: Boolean = false,
                       visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */

                       methodCfg: SilverCfg = null,
                       invariantContexts: Stack[Heap] = Stack.empty, // TODO: Merge

                       constrainableARPs: InsertionOrderedSet[Var] = InsertionOrderedSet.empty,
                       quantifiedVariables: Stack[Var] = Nil,
                       retrying: Boolean = false,
                       underJoin: Boolean = false,
                       functionRecorder: FunctionRecorder = NoopFunctionRecorder,
                       conservingSnapshotGeneration: Boolean = false,
                       recordPossibleTriggers: Boolean = false,
                       possibleTriggers: Map[ast.Exp, Term] = Map(),

                       triggerExp: Boolean = false,

                       partiallyConsumedHeap: Option[Heap] = None,
                       permissionScalingFactor: Term = terms.FullPerm(),

                       reserveHeaps: Stack[Heap] = Nil,
                       reserveCfgs: Stack[SilverCfg] = Stack(),
                       conservedPcs: Stack[Vector[RecordedPathConditions]] = Stack(),
                       recordPcs: Boolean = false,
                       exhaleExt: Boolean = false,

                       applyHeuristics: Boolean = false,
                       heuristicsDepth: Int = 0,
                       triggerAction: AnyRef = null,

                       ssCache: SsCache = Map.empty,
                       hackIssue387DisablePermissionConsumption: Boolean = false,

                       qpFields: InsertionOrderedSet[ast.Field] = InsertionOrderedSet.empty,
                       qpPredicates: InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty,
                       qpMagicWands: InsertionOrderedSet[MagicWandIdentifier] = InsertionOrderedSet.empty,
                       smCache: SnapshotMapCache = SnapshotMapCache.empty,
                       pmCache: PmCache = Map.empty,
                       smDomainNeeded: Boolean = false,
                       /* TODO: Isn't this data stable, i.e. fully known after a preprocessing step? If so, move it to the appropriate supporter. */
                       predicateSnapMap: Map[ast.Predicate, terms.Sort] = Map.empty,
                       predicateFormalVarMap: Map[ast.Predicate, Seq[terms.Var]] = Map.empty,
                       isMethodVerification: Boolean = false)
    extends Mergeable[State] {

  def incCycleCounter(m: ast.Predicate) =
    if (recordVisited) copy(visited = m :: visited)
    else this

  def decCycleCounter(m: ast.Member) =
    if (recordVisited) {
      require(visited.contains(m))

      val (ms, others) = visited.partition(_ == m)
      copy(visited = ms.tail ::: others)
    }
  else
    this

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Iterable[Var], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

  def scalePermissionFactor(p: Term) =
    copy(permissionScalingFactor = terms.PermTimes(p, permissionScalingFactor))

  def merge(other: State): State =
    State.merge(this, other)

  def preserveAfterLocalEvaluation(post: State): State =
    State.preserveAfterLocalEvaluation(this, post)

  def functionRecorderQuantifiedVariables(): Seq[Var] =
    functionRecorder.data.fold(Seq.empty[Var])(_.arguments)

  def relevantQuantifiedVariables(filterPredicate: Var => Boolean): Seq[Var] = (
       functionRecorderQuantifiedVariables()
    ++ quantifiedVariables.filter(filterPredicate)
  )

  def relevantQuantifiedVariables(occurringIn: Seq[Term]): Seq[Var] =
    relevantQuantifiedVariables(x => occurringIn.exists(_.contains(x)))

  lazy val relevantQuantifiedVariables: Seq[Var] =
    relevantQuantifiedVariables(_ => true)

  override val toString = s"${this.getClass.getSimpleName}(...)"

}

object State {
  type OldHeaps = Map[String, Heap]
  val OldHeaps = Map

  def merge(s1: State, s2: State): State = {
    /* TODO: Instead of aborting with a pattern mismatch, all mismatches
     *       should be detected first (and accumulated), and afterwards a meaningful
     *       exception should be thrown. This would improve debugging significantly.
     */

    s1 match {
      /* Decompose state s1 */
      case State(g1, h1, oldHeaps1,
                 parallelizeBranches1,
                 recordVisited1, visited1,
                 methodCfg1, invariantContexts1,
                 constrainableARPs1,
                 quantifiedVariables1,
                 retrying1,
                 underJoin1,
                 functionRecorder1,
                 conservingSnapshotGeneration1,
                 recordPossibleTriggers1, possibleTriggers1,
                 triggerExp1,
                 partiallyConsumedHeap1,
                 permissionScalingFactor1,
                 reserveHeaps1, reserveCfgs1, conservedPcs1, recordPcs1, exhaleExt1,
                 applyHeuristics1, heuristicsDepth1, triggerAction1,
                 ssCache1, hackIssue387DisablePermissionConsumption1,
                 qpFields1, qpPredicates1, qpMagicWands1, smCache1, pmCache1, smDomainNeeded1,
                 predicateSnapMap1, predicateFormalVarMap1, hack) =>

        /* Decompose state s2: most values must match those of s1 */
        s2 match {
          case State(`g1`, `h1`, `oldHeaps1`,
                     `parallelizeBranches1`,
                     `recordVisited1`, `visited1`,
                     `methodCfg1`, `invariantContexts1`,
                     constrainableARPs2,
                     `quantifiedVariables1`,
                     `retrying1`,
                     `underJoin1`,
                     functionRecorder2,
                     `conservingSnapshotGeneration1`,
                     `recordPossibleTriggers1`, possibleTriggers2,
                     triggerExp2,
                     `partiallyConsumedHeap1`,
                     `permissionScalingFactor1`,
                     `reserveHeaps1`, `reserveCfgs1`, `conservedPcs1`, `recordPcs1`, `exhaleExt1`,
                     `applyHeuristics1`, `heuristicsDepth1`, `triggerAction1`,
                     ssCache2, `hackIssue387DisablePermissionConsumption1`,
                     `qpFields1`, `qpPredicates1`, `qpMagicWands1`, smCache2, pmCache2, `smDomainNeeded1`,
                     `predicateSnapMap1`, `predicateFormalVarMap1`, `hack`) =>

            val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
            val triggerExp3 = triggerExp1 && triggerExp2
            val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
            val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

            val smCache3 = smCache1.union(smCache2)
            val pmCache3 = pmCache1 ++ pmCache2

            val ssCache3 = ssCache1 ++ ssCache2

            s1.copy(functionRecorder = functionRecorder3,
                    possibleTriggers = possibleTriggers3,
                    triggerExp = triggerExp3,
                    constrainableARPs = constrainableARPs3,
                    ssCache = ssCache3,
                    smCache = smCache3,
                    pmCache = pmCache3)

          case _ =>
            val err = new StringBuilder()
            for (ix <- 0 until s1.productArity) yield {
              val e1 = s1.productElement(ix)
              val e2 = s2.productElement(ix)
              if (e1 != e2) {
                err ++= s"\n\tField index ${s1.productElementName(ix)} not equal"
                err ++= s"\n\t\t state1: $e1"
                err ++= s"\n\t\t state2: $e2"

              }
            }
            sys.error(s"State merging failed: unexpected mismatch between symbolic states: $err")
      }
    }
  }

  // Merges two iterables of A using the id B generated by id function A => B.
  // Iterables can contain for example store entries or heap chunks.
  // If both iterables contain an entry with the same id, apply fTwice.
  // If only one iterable contains an entry with some id, apply fOnce.
  // Additional data of type C can be given to fOnce and fTwice, for example the respective path conditions.
  def mergeUsing[A, B, C, D](l1: Iterable[A], c1: C, l2: Iterable[A], c2: C)
                         (id: A => B)
                         (fOnce: (A, C) => Option[A])
                         (fTwice: (A, C, A, C) => Option[A])
                         : Iterable[A] = {

    val map1 = HashMap.from(l1.map(e => (id(e), e)))
    val map2 = HashMap.from(l2.map(e => (id(e), e)))

    map1.flatMap({ case (k, v1) => map2.get(k) match {
      case Some(v2) => fTwice(v1, c1, v2, c2)
      case None => fOnce(v1, c1)
    } }) ++ map2.flatMap({ case (k, v2) => map1.get(k) match {
      case Some(_) => None // Already considered in first case: Some(fTwice(v1, c1, v2, c2))
      case None => fOnce(v2, c2)
    } })
  }

  /*
  def mergeUsing[K, V, D](map1: Map[K, V], data1: D, map2: Map[K, V], data2: D)
                         (fOnce: (V, D) => Option[V])
                         (fTwice: (V, D, V, D) => Option[V])
                         : Map[K, V] = {

    map1.flatMap({ case (k, v1) =>
      (map2.get(k) match {
        case Some(v2) => fTwice(v1, data1, v2, data2)
        case None => fOnce(v1, data1)
      }).map(v => (k, v))
    }) ++ map2.flatMap({ case (k, v2) =>
      (map1.get(k) match {
        case Some(_) => None // Already considered in first case: Some(fTwice(v1, c1, v2, c2))
        case None => fOnce(v2, data2)
      }).map(v => (k, v))
    })
  }
  */

  def conditionalizeChunks(h: Iterable[Chunk], cond: Term) = {
    h map (c => {
      c match {

        case c: GeneralChunk =>
          c.withPerm(Ite(cond, c.perm, NoPerm()))
        /* Somehow this fails more tests than the above version
          val p = verifier.decider.fresh("perm", sorts.Perm)
          mergePcs :+= Implies(cond, p === c.perm)
          c.withPerm(p)
        */

        /* Z3 error: Unknown constant t

        case c: NonQuantifiedChunk =>
          val t = verifier.decider.fresh(c.snap.sort)
          mergePcs :+= Implies(cond, t === c.snap)
          c.withSnap(t)
        case c: QuantifiedChunk =>
          val t = verifier.decider.fresh(c.snapshotMap.sort)
          mergePcs :+= Implies(cond, t === c.snapshotMap)
          c.withSnapshotMap(t)
         */

        case _ => sys.error("Chunk type not conditionalizable.")
      }
    })
  }

  def mergeHeap(h1: Heap, cond1: Term, h2: Heap, cond2: Term) = {
    val (unconditionalHeapChunks, h1HeapChunksToConditionalize) = h1.values.partition(c1 => h2.values.find(_ == c1).nonEmpty)
    val h2HeapChunksToConditionalize = h2.values.filter(c2 => unconditionalHeapChunks.find(_ == c2).isEmpty)
    val h1ConditionalizedHeapChunks = conditionalizeChunks(h1HeapChunksToConditionalize, cond1)
    val h2ConditionalizedHeapChunks = conditionalizeChunks(h2HeapChunksToConditionalize, cond2)
    Heap(unconditionalHeapChunks) + Heap(h1ConditionalizedHeapChunks) + Heap(h2ConditionalizedHeapChunks)
  }

  def merge(s1: State, pc1: RecordedPathConditions, s2: State, pc2: RecordedPathConditions, verifier: Verifier): State = {
    /* TODO: Instead of aborting with a pattern mismatch, all mismatches
     *       should be detected first (and accumulated), and afterwards a meaningful
     *       exception should be thrown. This would improve debugging significantly.
     */

    //val cs1 = stateConsolidator.consolidate(s1, verifier)
    //val cs2 = stateConsolidator.consolidate(s2, verifier)
    //val cs1 = s1
    //val cs2 = s2
    println("MERGE")

    s1 match {
      /* Decompose state s1 */
      case State(g1, h1, oldHeaps1,
      parallelizeBranches1,
      recordVisited1, visited1,
      methodCfg1, invariantContexts1,
      constrainableARPs1,
      quantifiedVariables1,
      retrying1,
      underJoin1,
      functionRecorder1,
      conservingSnapshotGeneration1,
      recordPossibleTriggers1, possibleTriggers1,
      triggerExp1,
      partiallyConsumedHeap1,
      permissionScalingFactor1,
      reserveHeaps1, reserveCfgs1, conservedPcs1, recordPcs1, exhaleExt1,
      applyHeuristics1, heuristicsDepth1, triggerAction1,
      ssCache1, hackIssue387DisablePermissionConsumption1,
      qpFields1, qpPredicates1, qpMagicWands1, smCache1, pmCache1, smDomainNeeded1,
      predicateSnapMap1, predicateFormalVarMap1, hack) =>

        /* Decompose state s2: most values must match those of s1 */
        s2 match {
          case State(g2, h2, oldHeaps2,
          `parallelizeBranches1`,
          `recordVisited1`, `visited1`,
          `methodCfg1`, `invariantContexts1`,
          constrainableARPs2,
          `quantifiedVariables1`,
          `retrying1`,
          `underJoin1`,
          functionRecorder2,
          `conservingSnapshotGeneration1`,
          `recordPossibleTriggers1`, possibleTriggers2,
          triggerExp2,
          partiallyConsumedHeap2,
          `permissionScalingFactor1`,
          `reserveHeaps1`, `reserveCfgs1`, `conservedPcs1`, `recordPcs1`, `exhaleExt1`,
          `applyHeuristics1`, `heuristicsDepth1`, `triggerAction1`,
          ssCache2, `hackIssue387DisablePermissionConsumption1`,
          `qpFields1`, `qpPredicates1`, `qpMagicWands1`, smCache2, pmCache2, `smDomainNeeded1`,
          `predicateSnapMap1`, `predicateFormalVarMap1`, `hack`) =>

            val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
            val triggerExp3 = triggerExp1 && triggerExp2
            val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
            val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

            //val smCache3 = smCache1.union(smCache2)
            //val pmCache3 = pmCache1 ++ pmCache2

            //val ssCache3 = ssCache1 ++ ssCache2

            val conditions1 = And(pc1.branchConditions)
            val conditions2 = And(pc2.branchConditions)
            //println(s"cond1: $conditions1, cond2: $conditions2")

            var mergePcs: Vector[Term] = Vector.empty

            val mergeStore = (g1: Store, g2: Store) => {
              Store(mergeUsing(g1.values, conditions1, g2.values, conditions2)
              (_._1)
              ((entry, cond) => {
                /*
                // (k, t) is not needed
                val k = entry._1
                val v = entry._2
                val t = verifier.decider.fresh(v.sort)
                mergePcs :+= Implies(cond, Equals(t, v))
                (k, t)
                 */
                None
              })
              ((entry1, cond1, entry2, cond2) => {
                if (entry1 == entry2) {
                  //println(s"merging store, same entries: entry1 = ${entry1}, cond1 = ${cond1}, entry2 = ${entry2}, cond2 = ${cond2}")
                  Some(entry1)
                } else {
                  //println(s"merging store: entry1 = ${entry1}, cond1 = ${cond1}, entry2 = ${entry2}, cond2 = ${cond2}")
                  assert(entry1._1 == entry2._1)
                  assert(entry1._2.sort == entry2._2.sort)
                  val k = entry1._1
                  val v1 = entry1._2
                  val v2 = entry2._2
                  val t = verifier.decider.fresh(v1.sort)
                  //println(s"new entry: $k = $t")
                  mergePcs :+= Implies(cond1, Equals(t, v1))
                  mergePcs :+= Implies(cond2, Equals(t, v2))
                  Some((k, t))
                }
              }))
            }


            /*
            // ChunkKeys are used to correctly merge heap chunks.
            // Chunks with the same ChunkKey are merged together.
            trait ChunkKey
            case class QuantifiedChunkKey(quantifiedVars: Seq[Var], id: ChunkIdentifer) extends ChunkKey // TODO
            case class NonQuantifiedChunkKey(args: Seq[Term], id: ChunkIdentifer) extends ChunkKey

            val mergeHeap = (h1: Heap, h2: Heap) => {
              Heap(mergeUsing(h1.values, conditions1, h2.values, conditions2)
              (_ match {
                case c: NonQuantifiedChunk => NonQuantifiedChunkKey(c.args, c.id)
                case c: QuantifiedChunk => QuantifiedChunkKey(c.quantifiedVars, c.id) // TODO
              })
              ((chunk, cond) => {
                chunk match {
                  case c: NonQuantifiedChunk => {
                    val t = verifier.decider.fresh("merge_1_nqc_t", c.snap.sort)
                    val p = verifier.decider.fresh("merge_1_nqc_p", sorts.Perm)
                    mergePcs :+= Implies(cond, And(Equals(t, c.snap), Equals(p, c.perm)))
                    Some(c.withSnap(t).withPerm(p))
                  }
                  case c: QuantifiedChunk => {
                    val t = verifier.decider.fresh("merge_1_qc_t", c.snapshotMap.sort)
                    val p = verifier.decider.fresh("merged_1_qc_p", sorts.Perm)
                    mergePcs :+= Implies(cond, And(Equals(t, c.snapshotMap), Equals(p, c.perm)))
                    Some(c.withSnapshotMap(t).withPerm(p))
                  }
                }
              })
              ((chunk1, cond1, chunk2, cond2) => {
                if (chunk1 == chunk2) {
                  //println(s"merging heap, same entries: chunk1 = ${chunk1}, cond1 = ${cond1}, chunk2 = ${chunk2}, cond2 = ${cond2}")
                  Some(chunk1)
                } else {
                  println(s"merging heap: chunk1 = ${chunk1}, cond1 = ${cond1}, chunk2 = ${chunk2}, cond2 = ${cond2}")
                  (chunk1, chunk2) match {
                    case (c1: NonQuantifiedChunk, c2: NonQuantifiedChunk) => {
                      assert(c1.snap.sort == c2.snap.sort)
                      val t = verifier.decider.fresh("merge_2_nqc_t", c1.snap.sort)
                      val p = verifier.decider.fresh("merge_2_nqc_p", sorts.Perm)
                      mergePcs :+= Implies(cond1, And(Equals(t, c1.snap), Equals(p, c1.perm)))
                      mergePcs :+= Implies(cond2, And(Equals(t, c2.snap), Equals(p, c2.perm)))
                      val c3 = c1.withSnap(t).withPerm(p)
                      println(s"new chunk: $c3")
                      Some(c3)
                    }
                    case (c1: QuantifiedChunk, c2: QuantifiedChunk) => {
                      assert(c1.snapshotMap.sort == c2.snapshotMap.sort)
                      val t = verifier.decider.fresh("merge_2_qc_t", c1.snapshotMap.sort)
                      val p = verifier.decider.fresh("merge_2_qc_p", sorts.Perm)
                      mergePcs :+= Implies(cond1, And(Equals(t, c1.snapshotMap), Equals(p, c1.perm)))
                      mergePcs :+= Implies(cond2, And(Equals(t, c2.snapshotMap), Equals(p, c2.perm)))
                      val c3 = c1.withSnapshotMap(t).withPerm(p)
                      println(s"new chunk: $c3")
                      Some(c3)
                    }
                    case _ => sys.error("Chunks have to be of the same type.")
                  }
                }
              }))
            }
            */

            /*
            val conditionalizeChunks = (h: Iterable[Chunk], cond: Term) => {
              h map (c => {
                c match {

                  case c: GeneralChunk =>
                    c.withPerm(Ite(cond, c.perm, NoPerm()))
                    /* Somehow this fails more tests than the above version
                      val p = verifier.decider.fresh("perm", sorts.Perm)
                      mergePcs :+= Implies(cond, p === c.perm)
                      c.withPerm(p)
                    */

                  /* Z3 error: Unknown constant t

                  case c: NonQuantifiedChunk =>
                    val t = verifier.decider.fresh(c.snap.sort)
                    mergePcs :+= Implies(cond, t === c.snap)
                    c.withSnap(t)
                  case c: QuantifiedChunk =>
                    val t = verifier.decider.fresh(c.snapshotMap.sort)
                    mergePcs :+= Implies(cond, t === c.snapshotMap)
                    c.withSnapshotMap(t)
                   */

                  case _ => sys.error("Chunk type not conditionalizable.")
                }
              })
            }

            val mergeHeap = (h1: Heap, cond1: Term, h2: Heap, cond2: Term) => {
              val (unconditionalHeapChunks, h1HeapChunksToConditionalize) = h1.values.partition(c1 => h2.values.find(_ == c1).nonEmpty)
              val h2HeapChunksToConditionalize = h2.values.filter(c2 => unconditionalHeapChunks.find(_ == c2).isEmpty)
              println(s"H1TOCOND CHUNKS: $h1HeapChunksToConditionalize")
              println(s"H2TOCOND CHUNKS: $h2HeapChunksToConditionalize")
              val h1ConditionalizedHeapChunks = conditionalizeChunks(h1HeapChunksToConditionalize, cond1)
              val h2ConditionalizedHeapChunks = conditionalizeChunks(h2HeapChunksToConditionalize, cond2)
              println(s"UNCOND CHUNKS: $unconditionalHeapChunks")
              println(s"H1COND CHUNKS: $h1ConditionalizedHeapChunks")
              println(s"H2COND CHUNKS: $h2ConditionalizedHeapChunks")
              Heap(unconditionalHeapChunks) + Heap(h1ConditionalizedHeapChunks) + Heap(h2ConditionalizedHeapChunks)
            }
            */

            val g3 = mergeStore(g1, g2)
            val h3 = mergeHeap(h1, conditions1, h2, conditions2)
            val partiallyConsumedHeap3 = mergeHeap(
              partiallyConsumedHeap1.getOrElse(Heap()), conditions1,
              partiallyConsumedHeap2.getOrElse(Heap()), conditions2,
            )

            val oldHeaps3 = Map.from(mergeUsing(oldHeaps1, conditions1, oldHeaps2, conditions2)
              (_._1)
              ((entry, cond) => {
                val k = entry._1
                val h = entry._2
                //Some((k, Heap(conditionalizeChunks(h.values, cond))))
                None
              })
              ((entry1, cond1, entry2, cond2) => {
                assert(entry1._1 == entry2._1)
                val k = entry1._1
                val h1 = entry1._2
                val h2 = entry2._2
                Some((k, mergeHeap(h1, cond1, h2, cond2)))
              }))



            // TODO:
            // val oldHeaps3 = (implmentation above correct?)
            // val invariantContexts3 = ???

            // val reserveHeaps3 = ???
            // val conservedPcs3 = ???

            //println(s"merge pcs: $mergePcs")

            //verifier.decider.prover.comment("Merged states")
            verifier.decider.assume(mergePcs)

            val s3 = s1.copy(functionRecorder = functionRecorder3,
              possibleTriggers = possibleTriggers3,
              triggerExp = triggerExp3,
              constrainableARPs = constrainableARPs3,
              // TODO: Merge caches.
              ssCache = Map.empty,
              smCache = SnapshotMapCache.empty,
              pmCache = Map.empty,
              g = g3,
              h = h3,
              oldHeaps = oldHeaps3,
              partiallyConsumedHeap = Some(partiallyConsumedHeap3))

            val s4 = stateConsolidator.consolidate(s3, verifier)
            //println(s"CONSOLIDATED ${s4.h.values}")
            s4
          case _ =>
            val err = new StringBuilder()
            for (ix <- 0 until s1.productArity) yield {
              val e1 = s1.productElement(ix)
              val e2 = s2.productElement(ix)
              if (e1 != e2) {
                err ++= s"\n\tField index ${s1.productElementName(ix)} not equal"
              }
            }
            sys.error(s"PC-aware state merging failed: unexpected mismatch between symbolic states: $err")
        }
    }
  }

  def preserveAfterLocalEvaluation(pre: State, post: State): State = {
    pre.copy(functionRecorder = post.functionRecorder,
             possibleTriggers = post.possibleTriggers,
             smCache = post.smCache,
             constrainableARPs = post.constrainableARPs)
  }

  def conflictFreeUnionOrAbort[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K,V] =
    viper.silicon.utils.conflictFreeUnion(m1, m2) match {
      case (m3, conflicts) if conflicts.isEmpty => m3
      case _ => sys.error("Unexpected mismatch between contexts")
    }

  def merge[M <: Mergeable[M]](candidate1: Option[M], candidate2: Option[M]): Option[M] =
    (candidate1, candidate2) match {
      case (Some(m1), Some(m2)) => Some(m1.merge(m2))
      case (None, None) => None
      case _ => sys.error("Unexpected mismatch between contexts")
    }
}
