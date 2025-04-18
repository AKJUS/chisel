// SPDX-License-Identifier: Apache-2.0

package chiselTests

import chisel3._
import chisel3.experimental.{annotate, AnyTargetable}
import chisel3.stage.ChiselGeneratorAnnotation
import circt.stage.ChiselStage
import firrtl.annotations.{ModuleTarget, SingleTargetAnnotation, Target}
import org.scalatest._
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers

/** These annotations and the IdentityTransform class serve as an example of how to write a
  * Chisel/Firrtl library
  */
case class IdentityAnnotation(target: Target, value: String) extends SingleTargetAnnotation[Target] {
  def duplicate(n: Target): IdentityAnnotation = this.copy(target = n)
}

object identify {
  def apply(component: AnyTargetable, value: String): Unit = {
    annotate(component)(Seq(IdentityAnnotation(component.toTarget, value)))
  }
}

/** A diamond circuit Top instantiates A and B and both A and B instantiate C
  * Illustrations of annotations of various components and modules in both
  * relative and absolute cases
  *
  * This is currently not much of a test, read the printout to see what annotations look like
  */
/**
  * This class has parameterizable widths, it will generate different hardware
  * @param widthC io width
  */
class ModC(widthC: Int) extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(widthC.W))
    val out = Output(UInt(widthC.W))
  })
  io.out := io.in

  identify(this, s"ModC($widthC)")

  identify(io.out, s"ModC(ignore param)")
}

/**
  * instantiates a C of a particular size, ModA does not generate different hardware
  * based on it's parameter
  * @param annoParam  parameter is only used in annotation not in circuit
  */
class ModA(annoParam: Int) extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt())
    val out = Output(UInt())
  })
  val modC = Module(new ModC(16))
  modC.io.in := io.in
  io.out := modC.io.out

  identify(this, s"ModA(ignore param)")

  identify(io.out, s"ModA.io.out($annoParam)")
  identify(io.out, s"ModA.io.out(ignore_param)")
}

class ModB(widthB: Int) extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(widthB.W))
    val out = Output(UInt(widthB.W))
  })
  val modC = Module(new ModC(widthB))
  modC.io.in := io.in
  io.out := modC.io.out

  identify(io.in, s"modB.io.in annotated from inside modB")
}

class TopOfDiamond extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  val x = Reg(UInt(32.W))
  val y = Reg(UInt(32.W))

  val modA = Module(new ModA(64))
  val modB = Module(new ModB(32))

  x := io.in
  modA.io.in := x
  modB.io.in := x

  y := modA.io.out + modB.io.out
  io.out := y

  identify(this, s"TopOfDiamond\nWith\nSome new lines")

  identify(modB.io.in, s"modB.io.in annotated from outside modB")
}

class DiamondTester extends Module {
  val dut = Module(new TopOfDiamond)

  stop()
}

class AnnotatingDiamondSpec extends AnyFreeSpec with Matchers {

  """|Diamond is an example of a module that has two sub-modules A and B who both instantiate their
     |own instances of module C.  This highlights the difference between specific and general
     |annotation scopes""".stripMargin - {

    """|annotations are not resolved at after circuit elaboration,
       |that happens only after emit has been called on circuit""".stripMargin in {

      val annos = (new ChiselStage)
        .execute(
          Array("--target-dir", "test_run_dir", "--target", "chirrtl"),
          Seq(ChiselGeneratorAnnotation(() => new TopOfDiamond))
        )
        .filter {
          case _: IdentityAnnotation => true
          case _ => false
        }
        .toSeq

      info("Found ten (10) 'IdentityAnnotation's")
      (annos should have).length(10)

      info("Found IdentityAnnotation targeting '~|ModC' with value 'ModC(16)'")
      annos should contain(IdentityAnnotation(ModuleTarget("ModC"), "ModC(16)"))

      info("Found IdentityAnnotation targeting '~|ModC_1:seen' with value 'ModC(32)'")
      annos should contain(IdentityAnnotation(ModuleTarget("ModC_1"), "ModC(32)"))
    }
  }
}
