// SPDX-License-Identifier: Apache-2.0

package firrtl
package annotations

import java.io.File

import firrtl.ir._

@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
case class InvalidAnnotationFileException(file: File, cause: FirrtlUserException = null)
    extends FirrtlUserException(s"$file", cause)
@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
case class UnrecogizedAnnotationsException(msg: String) extends FirrtlUserException(s"Unrecognized annotations $msg")
@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
case class InvalidAnnotationJSONException(msg: String) extends FirrtlUserException(msg)
@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
case class AnnotationFileNotFoundException(file: File)
    extends FirrtlUserException(
      s"Annotation file $file not found!"
    )
@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
case class AnnotationClassNotFoundException(className: String)
    extends FirrtlUserException(
      s"Annotation class $className not found! Please check spelling and classpath"
    )
@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
class UnserializableAnnotationException private (msg: String) extends FirrtlUserException(msg)
@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
object UnserializableAnnotationException {
  private def toMessage(pair: (Annotation, Throwable)): String =
    s"Failed to serialiaze annotation of type ${pair._1.getClass.getName} because '${pair._2.getMessage}'"
  private[firrtl] def apply(badAnnos: Seq[(Annotation, Throwable)]) = {
    require(badAnnos.nonEmpty)
    val msg = badAnnos.map(toMessage).mkString("\n  ", "\n  ", "\n")
    new UnserializableAnnotationException(msg)
  }
}

@deprecated("All APIs in package firrtl are deprecated.", "Chisel 7.0.0")
object AnnotationUtils {

  /** Returns true if a valid Module name */
  val SerializedModuleName = """([a-zA-Z_][a-zA-Z_0-9~!@#$%^*\-+=?/]*)""".r
  def validModuleName(s: String): Boolean = s match {
    case SerializedModuleName(name) => true
    case _                          => false
  }

  /** Returns true if a valid component/subcomponent name */
  val SerializedComponentName = """([a-zA-Z_][a-zA-Z_0-9\[\]\.~!@#$%^*\-+=?/]*)""".r
  def validComponentName(s: String): Boolean = s match {
    case SerializedComponentName(name) => true
    case _                             => false
  }

  /** Tokenizes a string with '[', ']', '.' as tokens, e.g.:
    *  "foo.bar[boo.far]" becomes Seq("foo" "." "bar" "[" "boo" "." "far" "]")
    */
  def tokenize(s: String): Seq[String] = s.find(c => "[].".contains(c)) match {
    case Some(_) =>
      val i = s.indexWhere(c => "[].".contains(c))
      s.slice(0, i) match {
        case "" => s(i).toString +: tokenize(s.drop(i + 1))
        case x  => x +: s(i).toString +: tokenize(s.drop(i + 1))
      }
    case None if s == "" => Nil
    case None            => Seq(s)
  }

  /** Given a serialized component/subcomponent reference, subindex, subaccess,
    *  or subfield, return the corresponding IR expression.
    *  E.g. "foo.bar" becomes SubField(Reference("foo", UnknownType), "bar", UnknownType)
    */
  def toExp(s: String): Expression = {
    def parse(tokens: Seq[String]): Expression = {
      val DecPattern = """(\d+)""".r
      def findClose(tokens: Seq[String], index: Int, nOpen: Int): Seq[String] = {
        if (index >= tokens.size) {
          Utils.error("Cannot find closing bracket ]")
        } else
          tokens(index) match {
            case "["               => findClose(tokens, index + 1, nOpen + 1)
            case "]" if nOpen == 1 => tokens.slice(1, index)
            case "]"               => findClose(tokens, index + 1, nOpen - 1)
            case _                 => findClose(tokens, index + 1, nOpen)
          }
      }
      def buildup(e: Expression, tokens: Seq[String]): Expression = tokens match {
        case "[" :: tail =>
          val indexOrAccess = findClose(tokens, 0, 0)
          val exp = indexOrAccess.head match {
            case DecPattern(d) => SubIndex(e, d.toInt, UnknownType)
            case _             => SubAccess(e, parse(indexOrAccess), UnknownType)
          }
          buildup(exp, tokens.drop(2 + indexOrAccess.size))
        case "." :: tail =>
          buildup(SubField(e, tokens(1), UnknownType), tokens.drop(2))
        case Nil => e
      }
      val root = Reference(tokens.head, UnknownType)
      buildup(root, tokens.tail)
    }
    if (validComponentName(s)) {
      parse(tokenize(s))
    } else {
      Utils.error(s"Cannot convert $s into an expression.")
    }
  }
}
