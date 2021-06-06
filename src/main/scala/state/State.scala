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
import viper.silicon.interfaces.state.{GeneralChunk, NonQuantifiedChunk, QuantifiedChunk}
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.{And, Equals, Implies, PermMin, Term, Var}
import viper.silicon.supporters.functions.{FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.{Map, Stack}
import scala.collection.mutable.HashMap
import viper.silicon.verifier.Verifier

final case class State(g: Store = Store(),
                       h: Heap = Heap(),
                       oldHeaps: OldHeaps = Map.empty,

                       parallelizeBranches: Boolean = false,

                       recordVisited: Boolean = false,
                       visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */

                       methodCfg: SilverCfg = null,
                       invariantContexts: Stack[Heap] = Stack.empty,

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

            println("Normal merge")

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
            sys.error("State merging failed: unexpected mismatch between symbolic states")
      }
    }
  }

  /*
  def merge(s1: State, pc1: RecordedPathConditions, s2: State, pc2: RecordedPathConditions): State = {
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
          case State(g2, h2, `oldHeaps1`,
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

            println("Better merge")

            val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
            val triggerExp3 = triggerExp1 && triggerExp2
            val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
            val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

            val smCache3 = smCache1.union(smCache2)
            val pmCache3 = pmCache1 ++ pmCache2

            val ssCache3 = ssCache1 ++ ssCache2

            val g3 = conditionalizedStore(g1, pc1) + conditionalizedStore(g2, pc2)
            val h3 = conditionalizedHeap(h1, pc1) + conditionalizedHeap(h2, pc2)

            s1.copy(functionRecorder = functionRecorder3,
              possibleTriggers = possibleTriggers3,
              triggerExp = triggerExp3,
              constrainableARPs = constrainableARPs3,
              ssCache = ssCache3,
              smCache = smCache3,
              pmCache = pmCache3,
              g = g3,
              h = h3)

          case _ =>
            sys.error("State merging failed: unexpected mismatch between symbolic states")
        }
    }
  }

  def conditionalizedStore(g: Store, pc: RecordedPathConditions): Store = {
    val condition = And(pc.branchConditions)
    Store(g.values.map({case (k, v) => (k, Implies(condition, v))}))
  }

  def conditionalizedHeap(h: Heap, pc: RecordedPathConditions): Heap = {
    val condition = And(pc.branchConditions)
    Heap(h.values.map(_ match {
      case c: BasicChunk => c.withSnap(Implies(condition, c.snap))
      case _ => sys.error("Conditionalizing chunks not yet fully supported.")
    }))
  }
  */

  // Merges two iterables of A using the id B generated by id function A => B.
  // Iterables can contain for example store entries or heap entries.
  // If both iterables contain an entry with the same id, apply fTwice.
  // If only one iterable contains an entry with some id, apply fOnce.
  // Additional data of type C can be given to fOnce and fTwice, for example the respective path conditions.
  def mergeUsing[A, B, C](l1: Iterable[A], c1: C, l2: Iterable[A], c2: C)
                         (id: A => B)
                         (fOnce: (A, C) => A)
                         (fTwice: (A, C, A, C) => A)
                         : Iterable[A] = {

    val map1 = HashMap.from(l1.map(e => (id(e), e)))
    val map2 = HashMap.from(l2.map(e => (id(e), e)))

    map1.flatMap({ case (k, v1) => map2.get(k) match {
      case Some(v2) => Some(fTwice(v1, c1, v2, c2))
      case None => Some(fOnce(v1, c1))
    } }) ++ map2.flatMap({ case (k, v2) => map1.get(k) match {
      case Some(_) => None // Already considered in first case: Some(fTwice(v1, c1, v2, c2))
      case None => Some(fOnce(v2, c2))
    } })
  }

  def merge(s1: State, pc1: RecordedPathConditions, s2: State, pc2: RecordedPathConditions, verifier: Verifier): State = {
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
          case State(g2, h2, `oldHeaps1`,
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

            val conditions1 = And(pc1.branchConditions)
            val conditions2 = And(pc2.branchConditions)
            var mergePcs = Seq.empty

            val g3 = Store(mergeUsing(g1.values, conditions1, g2.values, conditions2)
              (_._1)
              ((entry, cond) => {
                val k = entry._1
                val v = entry._2
                val t = verifier.decider.fresh(v.sort)
                mergePcs :+ Implies(cond, Equals(t, v))
                (k, t)
              })
              ((entry1, cond1, entry2, cond2) => {
                assert(entry1._1 == entry2._1)
                assert(entry1._2.sort == entry2._2.sort)
                val k = entry1._1
                val v1 = entry1._2
                val v2 = entry2._2
                val t = verifier.decider.fresh(v1.sort)
                mergePcs :+ Implies(cond1, Equals(t, v1))
                mergePcs :+ Implies(cond2, Equals(t, v2))
                (k, t)
              }))

            val h3 = Heap(mergeUsing(h1.values, conditions1, h2.values, conditions2)
              (_.asInstanceOf[GeneralChunk].id)
              ((chunk, cond) => {
                chunk match {
                  case c: NonQuantifiedChunk => {
                    val t = verifier.decider.fresh(c.snap.sort)
                    mergePcs :+ Implies(cond, Equals(t, c.snap))
                    c.withSnap(t)
                  }
                  case c2: QuantifiedChunk => {
                    sys.error("Join not implemented for quantified chunks.")
                  }
                }
              })
              ((chunk1, cond1, chunk2, cond2) => {
                chunk1 match {
                  case c1: NonQuantifiedChunk => {
                    chunk2 match {
                      case c2: NonQuantifiedChunk => {
                        // Join non-quantified chunks.
                        assert(c1.snap.sort == c2.snap.sort)
                        val t = verifier.decider.fresh(c1.snap.sort)
                        val c3 = c1.withSnap(t).withPerm(PermMin(c1.perm, c2.perm))
                        mergePcs :+ Implies(cond1, Equals(t, c1.snap))
                        mergePcs :+ Implies(cond2, Equals(t, c2.snap))
                        c3
                      }
                      case _ => sys.error("Chunks have to be of the same type.")
                    }
                  }
                  case c1: QuantifiedChunk => {
                    chunk2 match {
                      case c2: QuantifiedChunk => {
                        // Join quantified chunks.
                        sys.error("Join not implemented for quantified chunks.")
                      }
                      case _ => sys.error("Chunks have to be of the same type.")
                    }
                  }
                }
              }))

            /*
            // Merge the stores.
            for ((k, v2) <- g2.values) {
              g3.values.get(k) match {
                // If the chunks are the same, we don't need to do anything.
                case Some(v1) if v1 == v2 => {}
                case Some(v1) => {
                  // Update store entry k to new symbolic value t
                  // And constrain t depending on the branch conditions.
                  val t = Var(Identifier("id"), v1.sort)
                  joinPcs :+ Implies(conditions1, Equals(t, v1))
                  joinPcs :+ Implies(conditions2, Equals(t, v2))
                  g3 = g3 + (k, t)
                }
                case None => {
                  val t = Var(Identifier("id"), v2.sort)
                  joinPcs :+ Implies(conditions2, Equals(t, v2))
                  g3 = g3 + (k, t)
                }
              }
            }



            // Merge the heaps.
            for (c2 <- h2.values) {
              h3.values.find(c1 => c1.asInstanceOf[GeneralChunk].id == c2.asInstanceOf[GeneralChunk].id) match {
                // If the chunks are the same, we don't need to do anything.
                case Some(c1) if c1 == c2 => {}
                case Some(c1) => {
                  // Update heap chunk k to point to new symbolic value t
                  // And constrain t depending on the branch conditions.
                  c1 match {
                    case c1: NonQuantifiedChunk => {
                      c2 match {
                        case c2: NonQuantifiedChunk => {
                          // Join non-quantified chunks.
                          assert(c1.snap.sort == c2.snap.sort)
                          val t = Var(Identifier("id"), c1.snap.sort)
                          val c3 = c1.withSnap(t).withPerm(PermMin(c1.perm, c2.perm))
                          joinPcs :+ Implies(conditions1, Equals(t, c1.snap))
                          joinPcs :+ Implies(conditions2, Equals(t, c2.snap))
                          h3 = h3 + c3
                        }
                        case _ => sys.error("Chunks have to be of the same type.")
                      }
                    }
                    case c: QuantifiedChunk => {
                      c2 match {
                        case c2: QuantifiedChunk => {
                          // Join quantified chunks.
                          sys.error("Join not implemented for quantified chunks.")
                        }
                        case _ => sys.error("Chunks have to be of the same type.")
                      }
                    }
                  }
                }
                case None => {
                  c2 match {
                    case c2: NonQuantifiedChunk => {
                      val t = Var(Identifier("id"), c2.snap.sort)
                      val c3 = c2.withSnap(t)
                      joinPcs :+ Implies(conditions2, Equals(t, c2.snap))
                      h3 = h3 + c3
                    }
                    case c2: QuantifiedChunk => {
                      sys.error("Join not implemented for quantified chunks.")
                    }
                  }
                }
              }
            }
            */

            verifier.decider.prover.comment("Merged states")
            verifier.decider.assume(mergePcs)

            s1.copy(functionRecorder = functionRecorder3,
              possibleTriggers = possibleTriggers3,
              triggerExp = triggerExp3,
              constrainableARPs = constrainableARPs3,
              ssCache = ssCache3,
              smCache = smCache3,
              pmCache = pmCache3,
              g = g3,
              h = h3)
          case _ =>
            sys.error("State merging failed: unexpected mismatch between symbolic states")
        }
    }
  }


  def conditionalizedHeap(h: Heap, pc: RecordedPathConditions): Heap = {
    val condition = And(pc.branchConditions)
    Heap(h.values.map(_ match {
      case c: BasicChunk => c.withSnap(Implies(condition, c.snap))
      case _ => sys.error("Conditionalizing chunks not yet fully supported.")
    }))
  }

  // x.f -> a
  // x.f -> cond ? a : b

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
