// SPDX-License-Identifier: Apache-2.0
package chisel3.util

import firrtl.AttributeAnnotation
import firrtl.annotations.Named

import chisel3.Data
import chisel3.experimental.{annotate, requireIsAnnotatable}

/** Helper Object for applying Attribute Annotations */
object addAttribute {

  /** Add attribute annotation to a chisel target.
    *
    *  == Example ==
    *  {{{
    *  import chisel3._
    *  import chisel3.util.addAttribute
    *  class AttributeExample extends Module {
    *    val io = IO(new Bundle {
    *      val input = Input(UInt(8.W))
    *      val output = Output(UInt(8.W))
    *    })
    *
    *    val reg = RegNext(io.input)
    *
    *    addAttribute(reg, "synthesis translate_off")
    *
    *    io.output := reg
    *  }
    *
    *  }}}
    *
    * @param target Chisel target. Must be Reg, Wire, or RawModule type.
    * @param annoString attribute string to add to target.
    */
  def apply(target: Data, annoString: String): Unit = {
    annotate(target)(Seq(AttributeAnnotation(target.toNamed, annoString)))
  }
}
