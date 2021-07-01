// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.state.State
import viper.silicon.verifier.Verifier

case class ConsumerJoinDataEntry[D](s: State, data: D, pathConditions: RecordedPathConditions) {
  // Instead of merging states, we can directly merge JoinDataEntries to obtain new States.
  // This gives us more information about the path conditions.
  def pathConditionAwareMerge(other: ConsumerJoinDataEntry[D])(verifier: Verifier): State = {
    State.merge(this.s, this.pathConditions, other.s, other.pathConditions, verifier)
  }
}


object consumerJoiner {
  def join[D, JD](s: State, v: Verifier)
                 (block: (State, Verifier, (State, D, Verifier) => VerificationResult) => VerificationResult)
                 (merge: (Seq[ConsumerJoinDataEntry[D]], Verifier) => (State, JD))
                 (Q: (State, JD, Verifier) => VerificationResult)
  : VerificationResult = {

    var entries: Seq[ConsumerJoinDataEntry[D]] = Vector.empty

    executionFlowController.locally(s, v)((s1, v1) => {
      val preMark = v1.decider.setPathConditionMark()
      val s2 = s1.copy(underJoin = true)

      block(s2, v1, (s3, data, v2) => {
        entries :+= ConsumerJoinDataEntry(s3, data, v2.decider.pcs.after(preMark))
        println("done")
        Success()
      })
    }) && {
      println("join entries")
      if (entries.isEmpty) {
        /* No block data was collected, which we interpret as all branches through
         * the block being infeasible. In turn, we assume that the overall verification path
         * is infeasible. Instead of calling Q, we therefore terminate this path.
         */
        Success()
      } else {
        val (sJoined, dataJoined) = merge(entries, v)

        entries foreach (entry => {
          val pcs = entry.pathConditions.conditionalized
          v.decider.prover.comment("Joined path conditions")
          v.decider.assume(pcs)
        })

        Q(sJoined, dataJoined, v)
      }
    }
  }
}
