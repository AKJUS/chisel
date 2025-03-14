// SPDX-License-Identifier: Apache-2.0

package chisel3.stage.phases

import chisel3.layer.Layer
import chisel3.stage.{ChiselOutputFileAnnotation, PrintFullStackTraceAnnotation, RemapLayer}

import firrtl.AnnotationSeq
import firrtl.annotations.Annotation
import firrtl.options.{Dependency, OptionsException, Phase}

/** Sanity checks an [[firrtl.AnnotationSeq]] before running the main [[firrtl.options.Phase]]s of
  * `chisel3.stage.ChiselStage`.
  */
class Checks extends Phase {
  import firrtl.annoSeqToSeq

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = Seq.empty
  override def optionalPrerequisiteOf = Seq(Dependency[Elaborate])
  override def invalidates(a: Phase) = false

  def transform(annotations: AnnotationSeq): AnnotationSeq = {
    val st, outF, lm = collection.mutable.ListBuffer[Annotation]()
    annotations.foreach {
      case a: PrintFullStackTraceAnnotation.type => a +=: st
      case a: ChiselOutputFileAnnotation         => a +=: outF
      case a: RemapLayer                         => a +=: lm
      case _ =>
    }

    if (st.size > 1) {
      throw new OptionsException(
        s"""|At most one PrintFullStackTraceAnnotation can be specified, but found '${st.size}'. Did you duplicate:
            |    - option or annotation: --full-stacktrace, PrintFullStackTraceAnnotation
            |""".stripMargin
      )
    }

    if (outF.size > 1) {
      throw new OptionsException(
        s"""|At most one Chisel output file can be specified but found '${outF.size}'. Did you duplicate:
            |    - option or annotation: --chisel-output-file, ChiselOutputFileAnnotation
            |""".stripMargin
      )
    }

    val lmMap = collection.mutable.HashMap[Layer, Layer]()
    lm.foreach {
      case RemapLayer(oldLayer, newLayer) if lmMap.contains(oldLayer) =>
        throw new OptionsException(
          s"""|The same old layer, '$oldLayer' is renamed multiple times: '${lmMap(oldLayer)}' and '$newLayer'
              |""".stripMargin
        )
      case RemapLayer(oldLayer, newLayer) => lmMap += ((oldLayer, newLayer))
    }

    annotations
  }

}
