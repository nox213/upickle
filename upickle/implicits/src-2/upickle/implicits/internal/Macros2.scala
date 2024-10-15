package upickle.implicits.internal

import scala.annotation.{nowarn, StaticAnnotation}
import scala.language.experimental.macros
import compat._

import acyclic.file
import upickle.core.Annotator
import upickle.implicits.{MacrosCommon, flatten, key}
import language.higherKinds
import language.existentials

/**
 * Implementation of macros used by uPickle to serialize and deserialize
 * case classes automatically. You probably shouldn't need to use these
 * directly, since they are called implicitly when trying to read/write
 * types you don't have a Reader/Writer in scope for.
 */
@nowarn("cat=deprecation")
object Macros2 {

  trait DeriveDefaults[M[_]] {
    val c: scala.reflect.macros.blackbox.Context
    private def fail(tpe: c.Type, s: String) = c.abort(c.enclosingPosition, s)

    import c.universe._
    private def companionTree(tpe: c.Type): Tree = {
      val companionSymbol = tpe.typeSymbol.companionSymbol

      if (companionSymbol == NoSymbol && tpe.typeSymbol.isClass) {
        val clsSymbol = tpe.typeSymbol.asClass
        val msg = "[error] The companion symbol could not be determined for " +
          s"[[${clsSymbol.name}]]. This may be due to a bug in scalac (SI-7567) " +
          "that arises when a case class within a function is upickle. As a " +
          "workaround, move the declaration to the module-level."
        fail(tpe, msg)
      } else {
        val symTab = c.universe.asInstanceOf[reflect.internal.SymbolTable]
        val pre = tpe.asInstanceOf[symTab.Type].prefix.asInstanceOf[Type]
        c.universe.treeBuild.mkAttributedRef(pre, companionSymbol)
      }

    }

    /**
      * If a super-type is generic, find all the subtypes, but at the same time
      * fill in all the generic type parameters that are based on the super-type's
      * concrete type
      */
    private def fleshedOutSubtypes(tpe: Type) = {
      for{
        subtypeSym <- tpe.typeSymbol.asClass.knownDirectSubclasses.filter(!_.toString.contains("<local child>"))
        if subtypeSym.isType
        st = subtypeSym.asType.toType
        baseClsArgs = st.baseType(tpe.typeSymbol).asInstanceOf[TypeRef].args
      } yield {
        tpe match{
          case ExistentialType(_, TypeRef(pre, sym, args)) =>
            st.substituteTypes(baseClsArgs.map(_.typeSymbol), args)
          case ExistentialType(_, _) => st
          case TypeRef(pre, sym, args) =>
            st.substituteTypes(baseClsArgs.map(_.typeSymbol), args)
        }
      }
    }

    private def deriveObject(tpe: c.Type) = {
      val mod = tpe.typeSymbol.asClass.module
      val symTab = c.universe.asInstanceOf[reflect.internal.SymbolTable]
      val pre = tpe.asInstanceOf[symTab.Type].prefix.asInstanceOf[Type]
      val mod2 = c.universe.treeBuild.mkAttributedRef(pre, mod)

      annotate(tpe)(wrapObject(mod2))

    }

    private[upickle] def mergeTrait(tagKey: Option[String], subtrees: Seq[Tree], subtypes: Seq[Type], targetType: c.Type): Tree

    private[upickle] def derive(tpe: c.Type) = {
      if (tpe.typeSymbol.asClass.isTrait || (tpe.typeSymbol.asClass.isAbstractClass && !tpe.typeSymbol.isJava)) {
        val derived = deriveTrait(tpe)
        derived
      }
      else if (tpe.typeSymbol.isModuleClass) deriveObject(tpe)
      else deriveClass(tpe)
    }

    private def deriveTrait(tpe: c.Type): c.universe.Tree = {
      val clsSymbol = tpe.typeSymbol.asClass

      if (!clsSymbol.isSealed) {
        fail(tpe, s"[error] The referenced trait [[${clsSymbol.name}]] must be sealed.")
      }else if (clsSymbol.knownDirectSubclasses.filter(!_.toString.contains("<local child>")).isEmpty) {
        val msg =
          s"The referenced trait [[${clsSymbol.name}]] does not have any sub-classes. This may " +
            "happen due to a limitation of scalac (SI-7046). To work around this, " +
            "try manually specifying the sealed trait picklers as described in " +
            "https://com-lihaoyi.github.io/upickle/#ManualSealedTraitPicklers"
        fail(tpe, msg)
      }else{
        val tagKey = customKey(clsSymbol)
        val subTypes = fleshedOutSubtypes(tpe).toSeq.sortBy(_.typeSymbol.fullName)
        //    println("deriveTrait")
        val subDerives = subTypes.map(subCls => q"implicitly[${typeclassFor(subCls)}]")
        //    println(Console.GREEN + "subDerives " + Console.RESET + subDrivess)
        val merged = mergeTrait(tagKey, subDerives, subTypes, tpe)
        merged
      }
    }

    private[upickle] def typeclass: c.WeakTypeTag[M[_]]

    private def typeclassFor(t: Type) = {
      //    println("typeclassFor " + weakTypeOf[M[_]](typeclass))

      weakTypeOf[M[_]](typeclass) match {
        case TypeRef(a, b, _) =>
          import compat._
          TypeRef(a, b, List(t))
        case ExistentialType(_, TypeRef(a, b, _)) =>
          import compat._
          TypeRef(a, b, List(t))
        case x =>
          println("Dunno Wad Dis Typeclazz Is " + x)
          println(x)
          println(x.getClass)
          ???
      }
    }

    sealed trait Flatten

    object Flatten {
      case class Class(companion: Tree, fields: List[Field], varArgs: Boolean) extends Flatten
      case object Map extends Flatten
      case object None extends Flatten
    }

    case class Field(
      name: String,
      mappedName: String,
      tpe: Type,
      symbol: Symbol,
      defaultValue: Option[Tree],
      flatten: Flatten,
    ) {
      lazy val allFields: List[Field] = {
        def loop(field: Field): List[Field] =
          field.flatten match {
            case Flatten.Class(_, fields, _) => fields.flatMap(loop)
            case Flatten.Map => List(field)
            case Flatten.None => List(field)
          }
        loop(this)
      }
    }

    private def getFields(tpe: c.Type): (c.Tree, List[Field], Boolean) = {
      def applyTypeArguments(t: c.Type ): c.Type = {
        val typeParams = tpe.typeSymbol.asClass.typeParams
        val typeArguments = tpe.normalize.asInstanceOf[TypeRef].args
        if (t.typeSymbol != definitions.RepeatedParamClass) {
          t.substituteTypes(typeParams, typeArguments)
        } else {
          val TypeRef(pref, sym, _) = typeOf[Seq[Int]]
          internal.typeRef(pref, sym, t.asInstanceOf[TypeRef].args)
        }
      }

      val companion = companionTree(tpe)
      //tickle the companion members -- Not doing this leads to unexpected runtime behavior
      //I wonder if there is an SI related to this?
      companion.tpe.members.foreach(_ => ())
      tpe.members.find(x => x.isMethod && x.asMethod.isPrimaryConstructor) match {
        case None => fail(tpe, "Can't find primary constructor of " + tpe)
        case Some(primaryConstructor) =>
          val params = primaryConstructor.asMethod.paramLists.flatten
          val varArgs = params.lastOption.exists(_.typeSignature.typeSymbol == definitions.RepeatedParamClass)
          val fields = params.zipWithIndex.map { case (param, i) =>
            val name = param.name.decodedName.toString
            val mappedName = customKey(param).getOrElse(name)
            val tpeOfField = applyTypeArguments(param.typeSignature)
            val defaultValue = if (param.asTerm.isParamWithDefault)
              Some(q"$companion.${TermName("apply$default$" + (i + 1))}")
            else
              None
            val flatten = param.annotations.find(_.tree.tpe =:= typeOf[flatten]) match {
              case Some(_) =>
                if (tpeOfField.typeSymbol == typeOf[collection.immutable.Map[_, _]].typeSymbol) Flatten.Map
                else if (tpeOfField.typeSymbol.isClass && tpeOfField.typeSymbol.asClass.isCaseClass) {
                  val (nestedCompanion, fields, nestedVarArgs) = getFields(tpeOfField)
                  Flatten.Class(nestedCompanion, fields, nestedVarArgs)
                }
                else fail(tpeOfField,
                  s"""Invalid type for flattening: $tpeOfField.
                     | Flatten only works on case classes and Maps""".stripMargin)
              case None =>
                Flatten.None
            }
            Field(param.name.toString, mappedName, tpeOfField, param, defaultValue, flatten)
          }
          (companion, fields, varArgs)
      }
    }

    private def deriveClass(tpe: c.Type) = {
      val (companion, fields, varArgs) = getFields(tpe)
      // According to @retronym, this is necessary in order to force the
      // default argument `apply$default$n` methods to be synthesized
      companion.tpe.member(TermName("apply")).info

      val allFields = fields.flatMap(_.allFields)
      validateFlattenAnnotation(allFields)

      val derive =
        // Otherwise, reading and writing are kinda identical
        wrapCaseN(
          companion,
          fields,
          varArgs,
          targetType = tpe,
        )

      annotate(tpe)(derive)
    }

    private def validateFlattenAnnotation(fields: List[Field]): Unit = {
      if (fields.count(_.flatten == Flatten.Map) > 1) {
        fail(NoType, "Only one Map can be annotated with @upickle.implicits.flatten in the same level")
      }
      if (fields.map(_.mappedName).distinct.length != fields.length) {
        fail(NoType, "There are multiple fields with the same key")
      }
      if (fields.exists(field => field.flatten == Flatten.Map && !(field.tpe <:< typeOf[Map[String, _]]))) {
        fail(NoType, "The key type of a Map annotated with @flatten must be String.")
      }
    }

    /** If there is a sealed base class, annotate the derived tree in the JSON
      * representation with a class label.
      */
    private def annotate(tpe: c.Type)(derived: c.universe.Tree) = {
      val sealedParents = tpe.baseClasses.filter(_.asClass.isSealed)

      if (sealedParents.isEmpty) derived
      else {
        val tagKey = MacrosCommon.tagKeyFromParents(
          tpe.typeSymbol.name.toString,
          sealedParents,
          customKey,
          (_: c.Symbol).name.toString,
          fail(tpe, _),
        )

        val sealedClassSymbol: Option[Symbol] = sealedParents.find(_ == tpe.typeSymbol)
        val segments =
          sealedClassSymbol.toList.map(_.fullName.split('.')) ++
            sealedParents
            .flatMap(_.asClass.knownDirectSubclasses)
            .map(_.fullName.split('.'))


        // -1 because even if there is only one subclass, and so no name segments
        // are needed to differentiate between them, we want to keep at least
        // the rightmost name segment
        val identicalSegmentCount = Range(0, segments.map(_.length).max - 1)
          .takeWhile(i => segments.map(_.lift(i)).distinct.size == 1)
          .length

        val tagValue = customKey(tpe.typeSymbol)
          .getOrElse(TypeName(tpe.typeSymbol.fullName).decodedName.toString)

        val shortTagValue = customKey(tpe.typeSymbol)
          .getOrElse(
            TypeName(
              tpe.typeSymbol.fullName.split('.').drop(identicalSegmentCount).mkString(".")
            ).decodedName.toString
          )

        val tagKeyExpr = tagKey match {
          case Some(v) => q"$v"
          case None => q"${c.prefix}.tagName"
        }
        q"${c.prefix}.annotate($derived, $tagKeyExpr, $tagValue, $shortTagValue)"
      }
    }

    private def customKey(sym: c.Symbol): Option[String] = {
        sym.annotations
          .find(_.tpe == typeOf[key])
          .flatMap(_.scalaArgs.headOption)
          .map{case Literal(Constant(s)) => s.toString}
    }

    private[upickle] def serializeDefaults(sym: c.Symbol): Option[Boolean] = {
        sym.annotations
          .find(_.tpe == typeOf[upickle.implicits.serializeDefaults])
          .flatMap(_.scalaArgs.headOption)
          .map{case Literal(Constant(s)) => s.asInstanceOf[Boolean]}
    }

    private[upickle] def wrapObject(obj: Tree): Tree

    private[upickle] def wrapCaseN(companion: Tree,
                  fields: List[Field],
                  varargs: Boolean,
                  targetType: c.Type): Tree
  }

  abstract class Reading[M[_]] extends DeriveDefaults[M] {
    val c: scala.reflect.macros.blackbox.Context
    import c.universe._
    def wrapObject(t: c.Tree) = q"new ${c.prefix}.SingletonReader($t)"

    def wrapCaseN(companion: c.universe.Tree, fields: List[Field], varargs: Boolean, targetType: c.Type): c.universe.Tree = {
      val allowUnknownKeysAnnotation = targetType.typeSymbol
        .annotations
        .find(_.tree.tpe == typeOf[upickle.implicits.allowUnknownKeys])
        .flatMap(_.tree.children.tail.headOption)
        .map { case Literal(Constant(b)) => b.asInstanceOf[Boolean] }

      val allFields = fields.flatMap(_.allFields).toArray.filter(_.flatten != Flatten.Map)
      val (hasFlattenOnMap, valueTypeOfMap) = fields.flatMap(_.allFields).find(_.flatten == Flatten.Map) match {
        case Some(f) =>
          val TypeRef(_, _, _ :: valueType :: Nil) = f.tpe
          (true, valueType)
        case None => (false, NoType)
      }
      val numberOfFields = allFields.length
      val (localReaders, aggregates) = allFields.zipWithIndex.map { case (_, idx) =>
            (TermName(s"localReader$idx"), TermName(s"aggregated$idx"))
        }.unzip

      val fieldToId = allFields.zipWithIndex.toMap
      def constructClass(companion: c.universe.Tree, fields: List[Field],  varargs: Boolean): c.universe.Tree =
        q"""
           $companion.apply(
             ..${
               fields.map { field =>
                 field.flatten match {
                   case Flatten.Class(c, f, v) => constructClass(c, f, v)
                   case Flatten.Map =>
                     val termName = TermName(s"aggregatedMap")
                     q"$termName.toMap"
                   case Flatten.None =>
                     val idx = fieldToId(field)
                     val termName = TermName(s"aggregated$idx")
                     if (field == fields.last && varargs) q"$termName:_*"
                     else q"$termName"
                 }
               }
             }
           )
        """

      q"""
        ..${
          for (i <- allFields.indices)
          yield q"private[this] lazy val ${localReaders(i)} = implicitly[${c.prefix}.Reader[${allFields(i).tpe}]]"
        }
        ..${
          if (hasFlattenOnMap)
            List(
              q"private[this] lazy val localReaderMap = implicitly[${c.prefix}.Reader[$valueTypeOfMap]]",
            )
          else Nil
        }
        new ${c.prefix}.CaseClassReader[$targetType] {
          override def visitObject(length: Int, jsonableKeys: Boolean, index: Int) = new ${if (numberOfFields <= 64) tq"_root_.upickle.implicits.CaseObjectContext[$targetType]" else tq"_root_.upickle.implicits.HugeCaseObjectContext[$targetType]"}(${numberOfFields}) {
            ..${
              for (i <- allFields.indices)
              yield q"private[this] var ${aggregates(i)}: ${allFields(i).tpe} = _"
            }
            ..${
              if (hasFlattenOnMap)
                List(
                  q"private[this] lazy val aggregatedMap: scala.collection.mutable.ListBuffer[(String, $valueTypeOfMap)] = scala.collection.mutable.ListBuffer.empty",
                )
              else Nil
            }

            def storeAggregatedValue(currentIndex: Int, v: Any): Unit = currentIndex match {
              case ..${
                for (i <- aggregates.indices)
                  yield cq"$i => ${aggregates(i)} = v.asInstanceOf[${allFields(i).tpe}]"
                }
              case ..${
                  if (hasFlattenOnMap)
                    List(cq"-1 => aggregatedMap += currentKey -> v.asInstanceOf[$valueTypeOfMap]")
                  else Nil
                }
              case _ => throw new java.lang.IndexOutOfBoundsException(currentIndex.toString)
            }

            def visitKeyValue(s: Any) = {
              storeToMap = false
              currentKey = ${c.prefix}.objectAttributeKeyReadMap(s.toString).toString
              currentIndex = currentKey match {
                case ..${
                  for (i <- allFields.indices)
                    yield cq"${allFields(i).mappedName} => $i"
                }
                case _ =>
                  ${
                    (allowUnknownKeysAnnotation, hasFlattenOnMap) match {
                      case (_, true) => q"storeToMap = true; -1"
                      case (None, false) =>
                        q"""
                          if (${ c.prefix }.allowUnknownKeys) -1
                          else throw new _root_.upickle.core.Abort("Unknown Key: " + s.toString)
                        """
                      case (Some(false), false) => q"""throw new _root_.upickle.core.Abort(" Unknown Key: " + s.toString)"""
                      case (Some(true), false) => q"-1"
                    }
                  }
              }
            }

            def visitEnd(index: Int) = {
              ..${
                for(i <- allFields.indices if allFields(i).defaultValue.isDefined)
                  yield q"this.storeValueIfNotFound($i, ${allFields(i).defaultValue.get})"
              }

              // Special-case 64 because java bit shifting ignores any RHS values above 63
              // https://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.19
              if (${
                if (numberOfFields <= 64) q"this.checkErrorMissingKeys(${if (numberOfFields == 64) -1 else (1L << numberOfFields) - 1})"
                else q"this.checkErrorMissingKeys(${numberOfFields})"
              }) {
                this.errorMissingKeys(${numberOfFields}, ${allFields.map(_.mappedName)})
              }

              ${constructClass(companion, fields, varargs)}
            }

            def subVisitor: _root_.upickle.core.Visitor[_, _] = currentIndex match {
              case -1 =>
                ${
                  if (hasFlattenOnMap)
                    q"localReaderMap"
                  else
                    q"_root_.upickle.core.NoOpVisitor"
                }
              case ..${
                      for (i <- allFields.indices)
                        yield cq"$i => ${localReaders(i)} "
                    }
              case _ => throw new java.lang.IndexOutOfBoundsException(currentIndex.toString)
            }
          }
        }
      """
    }

    override def mergeTrait(tagKey: Option[String], subtrees: Seq[Tree], subtypes: Seq[Type], targetType: c.Type): Tree = {
      val tagKeyExpr = tagKey match {
        case Some(v) => q"$v"
        case None => q"${c.prefix}.tagName"
      }
      q"${c.prefix}.Reader.merge[$targetType]($tagKeyExpr, ..$subtrees)"
    }
  }

  abstract class Writing[M[_]] extends DeriveDefaults[M] {
    val c: scala.reflect.macros.blackbox.Context
    import c.universe._
    def wrapObject(obj: c.Tree) = q"new ${c.prefix}.SingletonWriter($obj)"

    def internal = q"${c.prefix}.Internal"

    def wrapCaseN(companion: c.universe.Tree, fields: List[Field], varargs: Boolean, targetType: c.Type): c.universe.Tree = {
      def serDfltVals(field: Field) = {
        val b: Option[Boolean] = serializeDefaults(field.symbol).orElse(serializeDefaults(targetType.typeSymbol))
        b match {
          case Some(b) => q"${b}"
          case None => q"${c.prefix}.serializeDefaults"
        }
      }

      def write(field: Field, outer: c.universe.Tree): List[c.universe.Tree] = {
        val select = Select(outer, TermName(field.name))
        field.flatten match {
          case Flatten.Class(_, fields, _) =>
            fields.flatMap(write(_, select))
          case Flatten.Map =>
            val TypeRef(_, _, _ :: valueType :: Nil) = field.tpe
            q"""
               $select.foreach { case (key, value) =>
                 this.writeSnippetMappedName[R, $valueType](
                   ctx,
                   key.toString,
                   implicitly[${c.prefix}.Writer[$valueType]],
                   value
                 )
               }
             """ :: Nil
          case Flatten.None =>
            val snippet =
              q"""
            this.writeSnippetMappedName[R, ${field.tpe}](
               ctx,
               ${c.prefix}.objectAttributeKeyWriteMap(${field.mappedName}),
               implicitly[${c.prefix}.Writer[${field.tpe}]],
               $select
             )
            """
            val default = if (field.defaultValue.isEmpty) snippet
            else q"""if (${serDfltVals(field)} || $select != ${field.defaultValue.get}) $snippet"""
            default :: Nil
        }
      }

      def getLength(field: Field, outer: c.universe.Tree): List[c.universe.Tree] = {
        val select = Select(outer, TermName(field.name))
        field.flatten match {
          case Flatten.Class(_, fields, _) => fields.flatMap(getLength(_, select))
          case Flatten.Map => q"${select}.size" :: Nil
          case Flatten.None =>
            (
              if (field.defaultValue.isEmpty) q"1"
              else q"""if (${serDfltVals(field)} || ${select} != ${field.defaultValue}.get) 1 else 0"""
            ) :: Nil
        }
      }

      q"""
        new ${c.prefix}.CaseClassWriter[$targetType]{
          def length(v: $targetType) = {
            ${
              fields.flatMap(getLength(_, q"v"))
                .foldLeft[Tree](q"0") { case (prev, next) => q"$prev + $next" }
            }
          }
          override def write0[R](out: _root_.upickle.core.Visitor[_, R], v: $targetType): R = {
            if (v == null) out.visitNull(-1)
            else {
              val ctx = out.visitObject(length(v), true, -1)
              ..${fields.flatMap(write(_, q"v"))}
              ctx.visitEnd(-1)
            }
          }
          def writeToObject[R](ctx: _root_.upickle.core.ObjVisitor[_, R],
                               v: $targetType): Unit = {
            ..${fields.flatMap(write(_, q"v"))}
          }
        }
      """
    }

    override def mergeTrait(tagKey: Option[String], subtree: Seq[Tree], subtypes: Seq[Type], targetType: c.Type): Tree = {
      q"${c.prefix}.Writer.merge[$targetType](..$subtree)"
    }
  }
  def macroRImpl[T, R[_]](c0: scala.reflect.macros.blackbox.Context)
                         (implicit e1: c0.WeakTypeTag[T], e2: c0.WeakTypeTag[R[_]]): c0.Expr[R[T]] = {
    import c0.universe._
    val res = new Reading[R]{
      val c: c0.type = c0
      def typeclass = e2
    }.derive(e1.tpe)
//    println(c0.universe.showCode(res))
    c0.Expr[R[T]](res)
  }

  def macroWImpl[T, W[_]](c0: scala.reflect.macros.blackbox.Context)
                         (implicit e1: c0.WeakTypeTag[T], e2: c0.WeakTypeTag[W[_]]): c0.Expr[W[T]] = {
    import c0.universe._
    val res = new Writing[W]{
      val c: c0.type = c0
      def typeclass = e2
    }.derive(e1.tpe)
//    println(c0.universe.showCode(res))
    c0.Expr[W[T]](res)
  }
}

