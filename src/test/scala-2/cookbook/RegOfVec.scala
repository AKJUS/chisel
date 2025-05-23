// SPDX-License-Identifier: Apache-2.0

package cookbook

import chisel3._
import chisel3.simulator.stimulus.RunUntilFinished

/* ### How do I create a Reg of type Vec?
 *
 * For information, please see the API documentation for Vec
 * (https://chisel.eecs.berkeley.edu/api/index.html#chisel3.Vec)
 */
class RegOfVec extends CookbookTester(2) {
  // Reg of Vec of 32-bit UInts without initialization
  val regOfVec = Reg(Vec(4, UInt(32.W)))
  regOfVec(0) := 123.U // a couple of assignments
  regOfVec(2) := regOfVec(0)

  // Reg of Vec of 32-bit UInts initialized to zero
  //   Note that Seq.fill constructs 4 32-bit UInt literals with the value 0
  //   Vec(...) then constructs a Wire of these literals
  //   The Reg is then initialized to the value of the Wire (which gives it the same type)
  val initRegOfVec = RegInit(VecInit(Seq.fill(4)(0.U(32.W))))

  // Simple test (cycle comes from superclass)
  when(cycle === 2.U) { assert(regOfVec(2) === 123.U) }
  for (elt <- initRegOfVec) { assert(elt === 0.U) }
}

class RegOfVecSpec extends CookbookSpec {
  "RegOfVec" should "work" in {
    simulate(new RegOfVec)(RunUntilFinished(4))
  }
}
