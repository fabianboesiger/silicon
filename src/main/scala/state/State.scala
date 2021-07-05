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
import viper.silicon.rules.stateConsolidator
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.{And, Equals, Implies, Ite, NoPerm, Term, Var, sorts}
import viper.silicon.supporters.functions.{FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.{Map, Stack}
import viper.silicon.verifier.Verifier

final case class State(g: Store = Store(),
                       h: Heap = Heap(),
                       oldHeaps: OldHeaps = Map.empty,

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
            println("State merging failed in pure merge.")
            println(s1.conservedPcs)
            println(s2.conservedPcs)
            println(s1.conservedPcs == s2.conservedPcs)
            generateStateMismatchErrorMessage(s1, s2)
      }
    }
  }

  private def generateStateMismatchErrorMessage(s1: State, s2: State): Nothing = {
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

  // Merges two maps based on fOnce, if entry only exists in one map,
  // and fTwice if entry exists in both maps.
  private def mergeMaps[K, V, D](map1: Map[K, V], data1: D, map2: Map[K, V], data2: D)
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


  private def conditionalizeChunks(h: Iterable[Chunk], cond: Term, v: Verifier): Iterable[Chunk] = {
    h map (c => {
      c match {

        case c: GeneralChunk =>
          c.withPerm(Ite(cond, c.perm, NoPerm()))
          //Somehow this fails more tests than the above version
          /*
          val p = v.decider.fresh("perm", sorts.Perm)
          v.decider.assume(Implies(cond, p === c.perm))
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

  private def conditionalizeHeap(h: Heap, cond: Term, v: Verifier): Heap = {
    Heap(conditionalizeChunks(h.values, cond, v))
  }

  def mergeHeap(h1: Heap, cond1: Term, h2: Heap, cond2: Term, v: Verifier): Heap = {
    val (unconditionalHeapChunks, h1HeapChunksToConditionalize) = h1.values.partition(c1 => h2.values.exists(_ == c1))
    val h2HeapChunksToConditionalize = h2.values.filter(c2 => !unconditionalHeapChunks.exists(_ == c2))
    val h1ConditionalizedHeapChunks = conditionalizeChunks(h1HeapChunksToConditionalize, cond1, v)
    val h2ConditionalizedHeapChunks = conditionalizeChunks(h2HeapChunksToConditionalize, cond2, v)
    Heap(unconditionalHeapChunks) + Heap(h1ConditionalizedHeapChunks) + Heap(h2ConditionalizedHeapChunks)
  }

  def merge(s1: State, pc1: RecordedPathConditions, s2: State, pc2: RecordedPathConditions, verifier: Verifier): State = {

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
          `methodCfg1`, invariantContexts2,
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
          reserveHeaps2, `reserveCfgs1`, conservedPcs2, `recordPcs1`, `exhaleExt1`,
          `applyHeuristics1`, `heuristicsDepth1`, `triggerAction1`,
          ssCache2, `hackIssue387DisablePermissionConsumption1`,
          `qpFields1`, `qpPredicates1`, `qpMagicWands1`, smCache2, pmCache2, smDomainNeeded2,
          `predicateSnapMap1`, `predicateFormalVarMap1`, `hack`) =>

            val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
            val triggerExp3 = triggerExp1 && triggerExp2
            val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
            val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

            val smDomainNeeded3 = smDomainNeeded1 || smDomainNeeded2 // TODO: Use AND or OR to merge?

            val conditions1 = And(pc1.branchConditions)
            val conditions2 = And(pc2.branchConditions)

            //var mergePcs: Seq[Term] = Vector.empty

            val mergeStore = (g1: Store, g2: Store) => {
              Store(mergeMaps(g1.values, conditions1, g2.values, conditions2)
              ((_, _) => {
                // If store entry is only on one branch, we can safely discard it.
                None
              })
              ((v1, cond1, v2, cond2) => {
                if (v1 == v2) {
                  // Trivial: Both entries are the same.
                  Some(v1)
                } else {
                  assert(v1.sort == v2.sort)
                  // TODO: Is this faster?
                  //val t = verifier.decider.fresh(v1.sort)
                  //mergePcs :+= Implies(cond1, Equals(t, v1))
                  //mergePcs :+= Implies(cond2, Equals(t, v2))
                  //Some(t)
                  Some(Ite(cond1, v1, v2))
                }
              }))
            }

            val g3 = mergeStore(g1, g2)

            val h3 = mergeHeap(h1, conditions1, h2, conditions2, verifier)

            val partiallyConsumedHeap3 = (partiallyConsumedHeap1, partiallyConsumedHeap2) match {
              case (None, None) => None
              case (Some(pch1), None) => Some(conditionalizeHeap(pch1, conditions1, verifier))
              case (None, Some(pch2)) => Some(conditionalizeHeap(pch2, conditions2, verifier))
              case (Some(pch1), Some(pch2)) => Some(mergeHeap(
                  pch1, conditions1,
                  pch2, conditions2,
                  verifier
                ))
            }

            val oldHeaps3 = Map.from(mergeMaps(oldHeaps1, conditions1, oldHeaps2, conditions2)
              ((_, _) => {
                None
              })
              ((heap1, cond1, heap2, cond2) => {
                Some(mergeHeap(heap1, cond1, heap2, cond2, verifier))
              }))

            //verifier.decider.assume(mergePcs)

            // TODO: InvariantContexts should most likely be the same
            assert(invariantContexts1.length == invariantContexts2.length)
            val invariantContexts3 = invariantContexts1
              .zip(invariantContexts2)
              .map({case (h1, h2) => mergeHeap(h1, conditions1, h2, conditions2, verifier)})

            // TODO: Workout situations in which reserve heaps differ
            assert(reserveHeaps1.length == reserveHeaps2.length)
            val reserveHeaps3 = reserveHeaps1
              .zip(reserveHeaps2)
              .map({case (h1, h2) => mergeHeap(h1, conditions1, h2, conditions2, verifier)})


            assert(conservedPcs1.length == conservedPcs2.length)
            val conservedPcs3 = conservedPcs1
              .zip(conservedPcs1)
              .map({case (pcs1, pcs2) => (pcs1 ++ pcs2).distinct})

            //assert(conservedPcs1 == conservedPcs2)
            //val conservedPcs3 = conservedPcs1


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
              partiallyConsumedHeap = partiallyConsumedHeap3,
              smDomainNeeded = smDomainNeeded3,
              invariantContexts = invariantContexts3,
              reserveHeaps = reserveHeaps3,
              conservedPcs = conservedPcs3
            )

            val s4 = stateConsolidator.consolidate(s3, verifier)
            s4
          case _ => generateStateMismatchErrorMessage(s1, s2)
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
