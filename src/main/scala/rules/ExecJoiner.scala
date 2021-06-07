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

case class ExecJoinDataEntry(s: State, pathConditions: RecordedPathConditions) {
  // Instead of merging states, we can directly merge JoinDataEntries to obtain new States.
  // This gives us more information about the path conditions.
  def pathConditionAwareMerge(other: ExecJoinDataEntry)(verifier: Verifier): State = {
    State.merge(this.s, this.pathConditions, other.s, other.pathConditions, verifier)
  }
}

// Mostly the same as joiner, but merge takes a Verifier as an additional input argument.
// This allows us to do more complete state merges.
object execJoiner {
  def join(s: State, v: Verifier)
                 (block: (State, Verifier, (State, Verifier) => VerificationResult) => VerificationResult)
                 (merge: (Seq[ExecJoinDataEntry], Verifier) => State)
                 (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    var entries: Seq[ExecJoinDataEntry] = Vector.empty

    executionFlowController.locally(s, v)((s1, v1) => {
      val preMark = v1.decider.setPathConditionMark()
      val s2 = s1.copy(underJoin = true)

      block(s2, v1, (s3, v2) => {
        entries :+= ExecJoinDataEntry(s3, v2.decider.pcs.after(preMark))
        Success()
      })
    }) && {
      if (entries.isEmpty) {
        /* No block data was collected, which we interpret as all branches through
         * the block being infeasible. In turn, we assume that the overall verification path
         * is infeasible. Instead of calling Q, we therefore terminate this path.
         */
        Success()
      } else {
        val sJoined = merge(entries, v)

        entries foreach (entry => {
          val pcs = entry.pathConditions.conditionalized
          v.decider.prover.comment("Joined path conditions")
          v.decider.assume(pcs)
        })

        Q(sJoined, v)
      }
    }
  }
}
