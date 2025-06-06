// SPDX-License-Identifier: Apache-2.0

import firrtl.annotations.{IsMember, Named, ReferenceTarget}
import chisel3.internal.{ExceptionHelpers, NamedComponent}
import chisel3.experimental.BaseModule
import chisel3.experimental.hierarchy.Hierarchy

import java.util.{MissingFormatArgumentException, UnknownFormatConversionException}
import scala.collection.mutable
import scala.annotation.{nowarn, tailrec}

/** This package contains the main chisel3 API.
  */
package object chisel3 {
  import experimental.{DeprecatedSourceInfo, UnlocatableSourceInfo}
  import internal.firrtl.ir.Port
  import internal.Builder

  import scala.language.implicitConversions

  /**
    * These implicit classes allow one to convert [[scala.Int]] or [[scala.BigInt]] to
    * Chisel.UInt|Chisel.SInt by calling .asUInt|.asSInt on them, respectively.
    * The versions .asUInt(width)|.asSInt(width) are also available to explicitly
    * mark a width for the new literal.
    *
    * Also provides .asBool to scala.Boolean and .asUInt to String
    *
    * Note that, for stylistic reasons, one should avoid extracting immediately
    * after this call using apply, ie. 0.asUInt(1)(0) due to potential for
    * confusion (the 1 is a bit length and the 0 is a bit extraction position).
    * Prefer storing the result and then extracting from it.
    */
  implicit class fromBigIntToLiteral(bigint: BigInt) {

    /** Int to Bool conversion, allowing compact syntax like 1.B and 0.B
      */
    def B: Bool = bigint match {
      case bigint if bigint == 0 => Bool.Lit(false)
      case bigint if bigint == 1 => Bool.Lit(true)
      case bigint =>
        Builder.error(s"Cannot convert $bigint to Bool, must be 0 or 1")(UnlocatableSourceInfo)
        Bool.Lit(false)
    }

    /** Int to UInt conversion, recommended style for constants. */
    def U: UInt = UInt.Lit(bigint, Width()) // scalastyle:ignore method.name

    /** Int to SInt conversion, recommended style for constants. */
    def S: SInt = SInt.Lit(bigint, Width()) // scalastyle:ignore method.name

    /** Int to UInt conversion with specified width, recommended style for constants.
      */
    def U(width: Width): UInt = UInt.Lit(bigint, width)

    /** Int to SInt conversion with specified width, recommended style for constants.
      */
    def S(width: Width): SInt = SInt.Lit(bigint, width)

    /** Int to UInt conversion, recommended style for variables.
      */
    def asUInt: UInt = UInt.Lit(bigint, Width())

    /** Int to SInt conversion, recommended style for variables.
      */
    def asSInt: SInt = SInt.Lit(bigint, Width())

    /** Int to UInt conversion with specified width, recommended style for variables.
      */
    def asUInt(width: Width): UInt = UInt.Lit(bigint, width)

    /** Int to SInt conversion with specified width, recommended style for variables.
      */
    def asSInt(width: Width): SInt = SInt.Lit(bigint, width)
  }

  implicit class fromIntToLiteral(int: Int) extends fromBigIntToLiteral(int)
  implicit class fromLongToLiteral(long: Long) extends fromBigIntToLiteral(long)

  implicit class fromStringToLiteral(str: String) {

    /** String to UInt parse, recommended style for constants.
      */
    def U: UInt = str.asUInt

    /** String to UInt parse with specified width, recommended style for constants.
      */
    def U(width: Width): UInt = str.asUInt(width)

    /** String to UInt parse, recommended style for variables.
      */
    def asUInt: UInt = {
      val bigInt = parse(str)
      UInt.Lit(bigInt, Width(bigInt.bitLength.max(1)))
    }

    /** String to UInt parse with specified width, recommended style for variables.
      */
    def asUInt(width: Width): UInt = UInt.Lit(parse(str), width)

    protected def parse(n: String): BigInt = {
      val (base, num) = n.splitAt(1)
      val radix = base match {
        case "x" | "h" => 16
        case "d"       => 10
        case "o"       => 8
        case "b"       => 2
        case _         => Builder.error(s"Invalid base $base")(UnlocatableSourceInfo); 2
      }
      BigInt(num.filterNot(_ == '_'), radix)
    }
  }

  implicit class fromBooleanToLiteral(boolean: Boolean) {

    /** Boolean to Bool conversion, recommended style for constants.
      */
    def B: Bool = Bool.Lit(boolean)

    /** Boolean to Bool conversion, recommended style for variables.
      */
    def asBool: Bool = Bool.Lit(boolean)
  }

  implicit class fromIntToWidth(int: Int) {
    def W: Width = Width(int)
  }

  // Some possible regex replacements for the literal specifier deprecation:
  // (note: these are not guaranteed to handle all edge cases! check all replacements!)
  // Bool\((true|false)\)
  //  => $1.B
  // UInt\(width\s*=\s*(\d+|[_a-zA-Z][_0-9a-zA-Z]*)\)
  //  => UInt($1.W)
  // (UInt|SInt|Bits).width\((\d+|[_a-zA-Z][_0-9a-zA-Z]*)\)
  //  => $1($2.W)
  // (U|S)Int\((-?\d+|0[xX][0-9a-fA-F]+)\)
  //  => $2.$1
  // UInt\((\d+|0[xX][0-9a-fA-F]+),\s*(?:width\s*=)?\s*(\d+|[_a-zA-Z][_0-9a-zA-Z]*)\)
  //  => $1.U($2.W)
  // (UInt|SInt|Bool)\(([_a-zA-Z][_0-9a-zA-Z]*)\)
  //  => $2.as$1
  // (UInt|SInt)\(([_a-zA-Z][_0-9a-zA-Z]*),\s*(?:width\s*=)?\s*(\d+|[_a-zA-Z][_0-9a-zA-Z]*)\)
  //  => $2.as$1($3.W)

  /** Public API to access Node/Signal names.
    * currently, the node's name, the full path name, and references to its parent Module and component.
    * These are only valid once the design has been elaborated, and should not be used during its construction.
    */
  @deprecated("User-defined annotations are not supported in CIRCT, use Targetable if you must.", "Chisel 6.7.0")
  trait InstanceId {
    def instanceName:   String
    def pathName:       String
    def parentPathName: String
    def parentModName:  String

    /** Returns a FIRRTL Named that refers to this object in the elaborated hardware graph */
    def toNamed: Named

    /** Returns a FIRRTL IsMember that refers to this object in the elaborated hardware graph */
    def toTarget: IsMember

    /** Returns a FIRRTL IsMember that refers to the absolute path to this object in the elaborated hardware graph */
    def toAbsoluteTarget: IsMember
  }

  /** Implicit for custom Printable string interpolator */
  implicit class PrintableHelper(val sc: StringContext) extends AnyVal {

    /** Custom string interpolator for generating Printables: p"..."
      * mimicks s"..." for non-Printable data)
      */
    def p(args: Any*): Printable = {
      // P interpolator does not treat % differently - hence need to add % before sending to cf.
      val t = sc.parts.map(_.replaceAll("%", "%%"))
      StringContext(t: _*).cf(args: _*)
    }

    /** Custom string interpolator for generating formatted Printables : cf"..."
      *
      * Enhanced version of scala's `f` interpolator.
      * Each expression (argument) referenced within the string is
      * converted to a particular Printable depending
      * on the format specifier and type.
      *
      * ==== For Chisel types referenced within the String ====
      *
      *  - <code>%n</code> - Returns [[Name]] Printable.
      *  - <code>%N</code> - Returns [[FullName]] Printable.
      *  - <code>%b,%d,%x,%c</code> - Only applicable for types of [[Bits]] or derived from it. - returns ([[Binary]],[[Decimal]],
      * [[Hexadecimal]],[[Character]]) Printable respectively.
      *  - Default - If no specifier given call [[Data.toPrintable]] on the Chisel Type.
      *
      * ==== For [[Printable]] type:  ====
      *        No explicit format specifier supported - just return the Printable.
      *
      * ==== For regular scala types ====
      * Call String.format with the argument and specifier.
      * Default is %s if no specifier is given.
      * Wrap the result in [[PString]] Printable.
      *
      * ==== For the parts of the StringContext ====
      * Remove format specifiers and if literal percents (need to be escaped with %)
      * are present convert them into [[Percent]] Printable.
      * Rest of the string will be wrapped in [[PString]] Printable.
      *
      * @example
      * {{{
      *
      * val w1  = 20.U // Chisel UInt type (which extends Bits)
      * val f1 = 30.2 // Scala float type.
      * val pable = cf"w1 = $w1%x f1 = $f1%2.2f. This is 100%% clear"
      *
      * // the val `pable` is equivalent to the following
      * // Printables(List(PString(w1 = ), Hexadecimal(UInt<5>(20)), PString( f1 = ), PString(30.20), PString(. This is 100), Percent, PString( clear)))
      * }}}
      * throws UnknownFormatConversionException
      *         if literal percent not escaped with % or if the format specifier is not supported
      *         for the specific type
      *
      * throws StringContext.InvalidEscapeException
      *         if a `parts` string contains a backslash (`\`) character
      *         that does not start a valid escape sequence.
      *
      * throws IllegalArgumentException
      *         if the number of `parts` in the enclosing `StringContext` does not exceed
      *         the number of arguments `arg` by exactly 1.
      */
    @nowarn("msg=checkLengths in class StringContext is deprecated")
    def cf(args: Any*): Printable = {

      // Handle special escapes like %% and %m
      def escapeHandler(s: String): Seq[Printable] = {
        val pieces = mutable.ListBuffer.empty[Printable]
        def maybeAdd(start: Int, end: Int): Unit = {
          if (end > start) {
            pieces += PString(s.substring(start, end))
          }
        }
        var start = 0
        var end = 0
        while (end < s.length) {
          if (s(end) == '%') {
            val piece =
              if (end == s.length - 1) {
                throw new UnknownFormatConversionException("Trailing %")
              } else if (s(end + 1) == '%') {
                Percent
              } else if (s(end + 1) == 'm') {
                HierarchicalModuleName
              } else if (s(end + 1) == 'T') {
                SimulationTime
              } else {
                throw new UnknownFormatConversionException("Un-escaped %")
              }
            maybeAdd(start, end)
            pieces += piece
            start = end + 2
            end = start
          } else {
            end += 1
          }
        }
        maybeAdd(start, end)
        pieces.toList
      }

      def extractFormatSpecifier(part: String): (Option[String], String) = {
        // Check if part starts with a format specifier (with % - disambiguate with literal % checking the next character if needed to be %)
        // In the case of %f specifier there is a chance that we need more information - so capture till the 1st letter (a-zA-Z).
        // Example cf"This is $val%2.2f here" - parts - Seq("This is ","%2.2f here") - the format specifier here is %2.2f.
        val endFmtIdx =
          if (part.length > 1 && part(0) == '%' && !Printable.isNoArgSpecifier(part(1))) part.indexWhere(_.isLetter)
          else -1
        val (fmt, rest) = part.splitAt(endFmtIdx + 1)

        val fmtOpt = if (fmt.nonEmpty) Some(fmt) else None
        (fmtOpt, rest)

      }

      // TODO: Update this to current API when 2.12 is EOL
      sc.checkLengths(args) // Enforce sc.parts.size == pargs.size + 1
      val parts = sc.parts.map(StringContext.processEscapes)
      // The 1st part is assumed never to contain a format specifier.
      // If the 1st part of a string is an argument - then the 1st part will be an empty String.
      // So we need to parse parts following the 1st one to get the format specifiers if any
      val partsAfterFirst = parts.tail

      // Align parts to their potential specifiers
      val pables = partsAfterFirst.zip(args).flatMap {
        case (part, arg) => {
          val (fmt, modP) = extractFormatSpecifier(part)
          val fmtArg: Printable = arg match {
            case d: Data => {
              fmt match {
                case Some("%n") => Name(d)
                case Some("%N") => FullName(d)
                case Some(fForm) if d.isInstanceOf[Bits] =>
                  FirrtlFormat.parse(fForm, d.asInstanceOf[Bits]) match {
                    case Left(err) => throw new UnknownFormatConversionException(err)
                    case Right(p)  => p
                  }
                case Some(x) => {
                  val msg = s"Illegal format specifier '$x' for Chisel Data type!\n"
                  throw new UnknownFormatConversionException(msg)
                }
                case None => d.toPrintable
              }
            }
            case p: Printable => {
              fmt match {
                case Some(x) => {
                  val msg = s"Illegal format specifier '$x' for Chisel Printable type!\n"
                  throw new UnknownFormatConversionException(msg)
                }
                case None => p
              }
            }

            // Generic case - use String.format (for example %d,%2.2f etc on regular Scala types)
            case t => PString(fmt.getOrElse("%s").format(t))

          }
          Seq(fmtArg) ++ escapeHandler(modP)
        }
      }
      val result = escapeHandler(parts.head) ++ pables
      if (result.sizeIs == 1) result.head else Printables(result)
    }
  }

  type Connectable[T <: Data] = connectable.Connectable[T]

  val Connectable = connectable.Connectable

  implicit def string2Printable(str: String): Printable = PString(str)

  class InternalErrorException(message: String, cause: Throwable = null)
      extends ChiselException(
        "Internal Error: Please file an issue at https://github.com/chipsalliance/chisel3/issues:" + message,
        cause
      )

  class ChiselException(message: String, cause: Throwable = null) extends Exception(message, cause, true, true) {

    /** Examine a [[Throwable]], to extract all its causes. Innermost cause is first.
      * @param throwable an exception to examine
      * @return a sequence of all the causes with innermost cause first
      */
    @tailrec
    private def getCauses(throwable: Throwable, acc: Seq[Throwable] = Seq.empty): Seq[Throwable] =
      throwable.getCause() match {
        case null => throwable +: acc
        case a    => getCauses(a, throwable +: acc)
      }

    /** Returns true if an exception contains */
    private def containsBuilder(throwable: Throwable): Boolean =
      throwable
        .getStackTrace()
        .collectFirst {
          case ste if ste.getClassName().startsWith(ExceptionHelpers.builderName) => throwable
        }
        .isDefined

    /** Examine this [[ChiselException]] and it's causes for the first [[Throwable]] that contains a stack trace including
      * a stack trace element whose declaring class is the [[ExceptionHelpers.builderName]]. If no such element exists, return this
      * [[ChiselException]].
      */
    private lazy val likelyCause: Throwable =
      getCauses(this).collectFirst { case a if containsBuilder(a) => a }.getOrElse(this)

    /** For an exception, return a stack trace trimmed to user code only
      *
      * This does the following actions:
      *
      *   1. Trims the top of the stack trace while elements match [[ExceptionHelpers.packageTrimlist]]
      *   2. Trims the bottom of the stack trace until an element matches [[ExceptionHelpers.builderName]]
      *   3. Trims from the [[ExceptionHelpers.builderName]] all [[ExceptionHelpers.packageTrimlist]]
      *
      * @param throwable the exception whose stack trace should be trimmed
      * @return an array of stack trace elements
      */
    private def trimmedStackTrace(throwable: Throwable): Array[StackTraceElement] = {
      def isBlacklisted(ste: StackTraceElement) = {
        val packageName = ste.getClassName().takeWhile(_ != '.')
        ExceptionHelpers.packageTrimlist.contains(packageName)
      }

      val trimmedLeft = throwable.getStackTrace().view.dropWhile(isBlacklisted)
      val trimmedReverse = trimmedLeft.toIndexedSeq.reverse.view
        .dropWhile(ste => !ste.getClassName.startsWith(ExceptionHelpers.builderName))
        .dropWhile(isBlacklisted)
      trimmedReverse.toIndexedSeq.reverse.toArray
    }
  }

  // Debugger/Tester access to internal Chisel data structures and methods.
  def getDataElements(a: Aggregate): Seq[Element] = {
    a.allElements
  }
  class BindingException(message: String) extends ChiselException(message)

  /** A function expected a Chisel type but got a hardware object
    */
  case class ExpectedChiselTypeException(message: String) extends BindingException(message)

  /** A function expected a hardware object but got a Chisel type
    */
  case class ExpectedHardwareException(message: String) extends BindingException(message)

  /** A function expected annotatable hardware
    */
  case class ExpectedAnnotatableException(message: String) extends BindingException(message)

  /** An aggregate had a mix of specified and unspecified directionality children
    */
  case class MixedDirectionAggregateException(message: String) extends BindingException(message)

  /** Attempted to re-bind an already bound (directionality or hardware) object
    */
  case class RebindingException(message: String) extends BindingException(message)
  // Connection exceptions.
  case class BiConnectException(message: String) extends ChiselException(message)
  case class MonoConnectException(message: String) extends ChiselException(message)

  final val deprecatedMFCMessage =
    "this feature will not be supported as part of the migration to the MLIR-based FIRRTL Compiler (MFC). For more information about this migration, please see the Chisel ROADMAP.md."

  final val deprecatedPublicAPIMsg = "APIs in chisel3.internal are not intended to be public"

  /** Exposes target information and suggestName functionality of a NamedComponent.
    */
  // This is only currently used for SRAM to hide the underlying Memory but still let users annotate it.
  // Rather than generalizing this, it's more likely that we'll just delete it (and the use in SRAM) in favor of Path Properties.
  sealed trait HasTarget {
    def toTarget:                                                         ReferenceTarget
    def toAbsoluteTarget:                                                 ReferenceTarget
    def toRelativeTarget(root:            Option[BaseModule]):            ReferenceTarget
    def toRelativeTargetToHierarchy(root: Option[Hierarchy[BaseModule]]): ReferenceTarget

    /** Exposes the suggestName method of the NamedComponent so users can
      * provide a seed to influence the name generation of this component.
      *
      * @param seed seed for the name of this component
      */
    def suggestName(seed: String): Unit
  }

  object HasTarget {
    private[chisel3] case class Impl(t: SramTarget) extends HasTarget {
      def toTarget = t.toTarget
      def toAbsoluteTarget = t.toAbsoluteTarget
      def toRelativeTarget(root:            Option[BaseModule]) = t.toRelativeTarget(root)
      def toRelativeTargetToHierarchy(root: Option[Hierarchy[BaseModule]]) = t.toRelativeTargetToHierarchy(root)

      def suggestName(seed: String): Unit = t.suggestName(seed)
    }

    /** This wrapping hides the actual object, ensuring users only have access
      * to the target methods (instead of the type of the underlying object).
      */
    private[chisel3] def apply(t: SramTarget): HasTarget = Impl(t)

  }

  private def _withNameImpl[T](prevId: Long, name: String, nameMe: T): T = {
    chisel3.internal.Builder.nameRecursively(
      name,
      nameMe,
      (id: chisel3.internal.HasId, n: String) => {
        // Name override only if result was created in this scope
        if (id._id > prevId) {
          id.forceAutoSeed(n)
        }
      }
    )
    nameMe
  }

  /** Use Chisel's naming algorithm to name the returned value
    *
    * This will name typical "nameable" things like Chisel [[Data]], but only if the object is created in the thunk.
    * @param name The name to use
    * @param nameMe A thunk that returns the thing to be named
    * @tparam T The type of the thing to be named
    * @return The thing, possibly now named
    */
  def withName[T](name: String)(nameMe: => T): T = {
    // The _id of the most recently constructed HasId
    val prevId = Builder.idGen.value
    val result = nameMe
    _withNameImpl(prevId, name, result)
  }

  /** Use Chisel's naming algorithm to name values within the returned Product value
    *
    * This will name typical "nameable" things like Chisel [[Data]], but only for objects crated in the thunk.
    * @param names The names to use corresponding to interesting fields of the Product, empty Strings means no name
    * @param nameMe The [[scala.Product]] to be named
    * @tparam T The type of the thing to be named
    * @return The thing, with members possibly named
    */
  def withNames[T <: Product](names: String*)(nameMe: => T): T = {
    // The _id of the most recently constructed HasId
    val prevId = Builder.idGen.value
    val result = nameMe
    require(
      names.size == result.productArity,
      s"Number of names must match number of fields in Product, got ${names.size} and ${result.productArity}."
    )
    for ((name, t) <- names.iterator.zip(result.productIterator) if name.nonEmpty) {
      _withNameImpl(prevId, name, t)
    }
    result
  }
}
