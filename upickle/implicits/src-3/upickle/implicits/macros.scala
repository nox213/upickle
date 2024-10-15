package upickle.implicits.macros

import scala.quoted.{ given, _ }
import deriving._, compiletime._
import upickle.implicits.{MacrosCommon, ReadersVersionSpecific}

def getDefaultParamsImpl0[T](using Quotes, Type[T]): Map[String, Expr[AnyRef]] =
  import quotes.reflect._
  val unwrapped = TypeRepr.of[T] match {
    case AppliedType(p, v) => p
    case t => t
  }
  val sym = unwrapped.typeSymbol

  if (!sym.isClassDef) Map.empty
  else
    val comp =
      if (sym.isClassDef && !sym.companionClass.isNoSymbol ) sym.companionClass
      else sym

    val hasDefaults =
      for p <- sym.caseFields
      yield p.flags.is(Flags.HasDefault)

    val names = fieldLabelsImpl0[T].map(_._2).zip(hasDefaults).collect{case (n, true) => n}

    val body = comp.tree.asInstanceOf[ClassDef].body

    val idents: List[Term] =
      for case deff @ DefDef(name, _, _, _) <- body
      if name.startsWith("$lessinit$greater$default")
      yield TypeRepr.of[T] match{ // Fix copied from https://github.com/circe/circe/issues/2093
        case AppliedType(p, v) => Ref(deff.symbol).appliedToTypes(TypeRepr.of[T].typeArgs)
        case t => Ref(deff.symbol)
      }

    names.zip(idents.map(_.asExpr).map(e => '{$e.asInstanceOf[AnyRef]})).toMap

def extractKey[A](using Quotes)(sym: quotes.reflect.Symbol): Option[String] =
  import quotes.reflect._
  sym
    .annotations
    .find(_.tpe =:= TypeRepr.of[upickle.implicits.key])
    .map{case Apply(_, Literal(StringConstant(s)) :: Nil) => s}

def extractSerializeDefaults[A](using quotes: Quotes)(sym: quotes.reflect.Symbol): Option[Boolean] =
  import quotes.reflect._
  sym
    .annotations
    .find(_.tpe =:= TypeRepr.of[upickle.implicits.serializeDefaults])
    .map{case Apply(_, Literal(BooleanConstant(s)) :: Nil) => s}

inline def extractIgnoreUnknownKeys[T](): List[Boolean] = ${extractIgnoreUnknownKeysImpl[T]}
def extractIgnoreUnknownKeysImpl[T](using Quotes, Type[T]): Expr[List[Boolean]] =
  import quotes.reflect._
  Expr.ofList(
    TypeRepr.of[T].typeSymbol
      .annotations
      .find(_.tpe =:= TypeRepr.of[upickle.implicits.allowUnknownKeys])
      .map{case Apply(_, Literal(BooleanConstant(b)) :: Nil) => b}
      .map(Expr(_))
      .toList
    )

def extractFlatten[A](using Quotes)(sym: quotes.reflect.Symbol): Boolean =
  import quotes.reflect._
  sym
    .annotations
    .exists(_.tpe =:= TypeRepr.of[upickle.implicits.flatten])

inline def paramsCount[T]: Int = ${paramsCountImpl[T]}
def paramsCountImpl[T](using Quotes, Type[T]) = {
  import quotes.reflect._
  val fields = allFields[T]
  val count = fields.filter {case (_, _, _, _, flattenMap) => !flattenMap}.length
  Expr(count)
}

inline def allReaders[T, R[_]]: (AnyRef, Array[AnyRef]) = ${allReadersImpl[T, R]}
def allReadersImpl[T, R[_]](using Quotes, Type[T], Type[R]): Expr[(AnyRef, Array[AnyRef])] = {
  import quotes.reflect._
  val fields = allFields[T]
  val (readerMap, readers) = fields.partitionMap { case (_, _, tpe, _, isFlattenMap) =>
    if (isFlattenMap) {
      val valueTpe = tpe.typeArgs(1)
      val readerTpe = TypeRepr.of[R].appliedTo(valueTpe)
      val reader = readerTpe.asType match {
        case '[t] => '{summonInline[t].asInstanceOf[AnyRef]}
      }
      Left(reader)
    }
    else {
      val readerTpe = TypeRepr.of[R].appliedTo(tpe)
      val reader = readerTpe.asType match {
        case '[t] => '{summonInline[t].asInstanceOf[AnyRef]}
      }
      Right(reader)
    }
  }
  Expr.ofTuple(
    (
      readerMap.headOption.getOrElse('{null}.asInstanceOf[Expr[AnyRef]]), 
      '{${Expr.ofList(readers)}.toArray},
    )
  )
}

inline def allFieldsMappedName[T]: List[String] = ${allFieldsMappedNameImpl[T]}
def allFieldsMappedNameImpl[T](using Quotes, Type[T]): Expr[List[String]] = {
  import quotes.reflect._
  Expr(allFields[T].map { case (_, label, _, _, _) => label })
}

inline def storeDefaults[T](inline x: upickle.implicits.BaseCaseObjectContext): Unit = ${storeDefaultsImpl[T]('x)}
def storeDefaultsImpl[T](x: Expr[upickle.implicits.BaseCaseObjectContext])(using Quotes, Type[T]) = {
  import quotes.reflect.*
  val statements = allFields[T]
    .filter(!_._5)
    .zipWithIndex
    .map { case ((_, _, _, default, _), i) =>
      default match {
        case Some(defaultValue) => '{${x}.storeValueIfNotFound(${Expr(i)}, ${defaultValue})}
        case None => '{}
      }
    }

  Expr.block(statements, '{})
}

def allFields[T](using Quotes, Type[T]): List[(quotes.reflect.Symbol, String, quotes.reflect.TypeRepr, Option[Expr[Any]], Boolean)] = {
  import quotes.reflect._

  def loop(field: Symbol, label: String, classTypeRepr: TypeRepr, defaults: Map[String, Expr[Object]]): List[(Symbol, String, TypeRepr, Option[Expr[Any]], Boolean)] = {
    val flatten = extractFlatten(field)
    val substitutedTypeRepr = substituteTypeArgs(classTypeRepr, subsitituted = classTypeRepr.memberType(field))
    val typeSymbol = substitutedTypeRepr.typeSymbol
    if (flatten) {
      if (isMap(substitutedTypeRepr)) {
        (field, label, substitutedTypeRepr, defaults.get(label), true) :: Nil
      }
      else if (isCaseClass(typeSymbol)) {
        typeSymbol.typeRef.dealias.asType match {
          case '[t] =>
            fieldLabelsImpl0[t]
              .flatMap { case (rawLabel, label) =>
                val newDefaults = getDefaultParamsImpl0[t]
                val newClassTypeRepr = TypeRepr.of[T]
                loop(rawLabel, label, newClassTypeRepr, newDefaults)
              }
          case _ =>
            report.errorAndAbort(s"Unsupported type $typeSymbol for flattening")
        }
      } else report.errorAndAbort(s"${typeSymbol} is not a case class or a immutable.Map")
    }
    else {
      (field, label, substitutedTypeRepr, defaults.get(label), false) :: Nil
    }
  }

  fieldLabelsImpl0[T]
    .flatMap{ (rawLabel, label) =>
      val defaults = getDefaultParamsImpl0[T]
      val classTypeRepr = TypeRepr.of[T]
      loop(rawLabel, label, classTypeRepr, defaults)
    }
}

def fieldLabelsImpl0[T](using Quotes, Type[T]): List[(quotes.reflect.Symbol, String)] =
  import quotes.reflect._
  val fields: List[Symbol] = TypeRepr.of[T].typeSymbol
    .primaryConstructor
    .paramSymss
    .flatten
    .filterNot(_.isType)

  if (TypeRepr.of[T].isSingleton) Nil
  else fields.map{ sym =>
    extractKey(sym) match
    case Some(name) => (sym, name)
    case None => (sym, sym.name)
  }

inline def keyToIndex[T](inline x: String): Int = ${keyToIndexImpl[T]('x)}
def keyToIndexImpl[T](x: Expr[String])(using Quotes, Type[T]): Expr[Int] = {
  import quotes.reflect.*
  val fields = allFields[T].filter { case (_, _, _, _, isFlattenMap) => !isFlattenMap }
  val z = Match(
    x.asTerm,
    fields.zipWithIndex.map{case ((_, label, _, _, _), i) =>
      CaseDef(Literal(StringConstant(label)), None, Literal(IntConstant(i)))
    } ++ Seq(
      CaseDef(Wildcard(), None, Literal(IntConstant(-1)))
    )
  )

  z.asExpr.asInstanceOf[Expr[Int]]
}

inline def writeLength[T](inline thisOuter: upickle.core.Types with upickle.implicits.MacrosCommon,
                          inline v: T): Int =
  ${writeLengthImpl[T]('thisOuter, 'v)}

def serDfltVals(using quotes: Quotes)(thisOuter: Expr[upickle.core.Types with upickle.implicits.MacrosCommon],
                                      argSym: quotes.reflect.Symbol,
                                      targetType: quotes.reflect.Symbol): Expr[Boolean] = {
  extractSerializeDefaults(argSym).orElse(extractSerializeDefaults(targetType)) match {
    case Some(b) => Expr(b)
    case None => '{ ${ thisOuter }.serializeDefaults }
  }
}

def writeLengthImpl[T](thisOuter: Expr[upickle.core.Types with upickle.implicits.MacrosCommon],
                                       v: Expr[T])
                                      (using quotes: Quotes, t: Type[T]): Expr[Int] =
  import quotes.reflect.*
    def loop(field: Symbol, label: String, classTypeRepr: TypeRepr, select: Select, defaults: Map[String, Expr[Object]]): List[Expr[Int]] =  
      val flatten = extractFlatten(field)
      if (flatten) {
        val subsitituted = substituteTypeArgs(classTypeRepr, subsitituted = classTypeRepr.memberType(field))
        val typeSymbol = subsitituted.typeSymbol
        if (isMap(subsitituted)) {
          List(
            '{${select.asExprOf[Map[_, _]]}.size}
          )
        }
        else if (isCaseClass(typeSymbol)) {
          typeSymbol.typeRef.dealias.asType match {
            case '[t] =>
              fieldLabelsImpl0[t]
                .flatMap { case (rawLabel, label) =>
                  val newDefaults = getDefaultParamsImpl0[t]
                  val newSelect = Select.unique(select, rawLabel.name)
                  val newClassTypeRepr = TypeRepr.of[T]
                  loop(rawLabel, label, newClassTypeRepr, newSelect, newDefaults)
                }
            case _ =>
              report.errorAndAbort("Unsupported type for flattening")
          }
        } else report.errorAndAbort(s"${typeSymbol} is not a case class or a immutable.Map")
      }
      else if (!defaults.contains(label)) List('{1})
      else {
        val serDflt = serDfltVals(thisOuter, field, classTypeRepr.typeSymbol)
        List(
          '{if (${serDflt} || ${select.asExprOf[Any]} != ${defaults(label)}) 1 else 0}
        )
      }

    fieldLabelsImpl0[T]
      .flatMap { (rawLabel, label) =>
        val defaults = getDefaultParamsImpl0[T]
        val select = Select.unique(v.asTerm, rawLabel.name)
        val classTypeRepr = TypeRepr.of[T]
        loop(rawLabel, label, classTypeRepr, select, defaults)
      }
      .foldLeft('{0}) { case (prev, next) => '{$prev + $next} }

inline def writeSnippets[R, T, W[_]](inline thisOuter: upickle.core.Types with upickle.implicits.MacrosCommon,
                                   inline self: upickle.implicits.CaseClassReadWriters#CaseClassWriter[T],
                                   inline v: T,
                                   inline ctx: _root_.upickle.core.ObjVisitor[_, R]): Unit =
  ${writeSnippetsImpl[R, T, W]('thisOuter, 'self, 'v, 'ctx)}

def writeSnippetsImpl[R, T, W[_]](thisOuter: Expr[upickle.core.Types with upickle.implicits.MacrosCommon],
                            self: Expr[upickle.implicits.CaseClassReadWriters#CaseClassWriter[T]],
                            v: Expr[T],
                            ctx: Expr[_root_.upickle.core.ObjVisitor[_, R]])
                           (using Quotes, Type[T], Type[R], Type[W]): Expr[Unit] =

  import quotes.reflect.*

    def loop(field: Symbol, label: String, classTypeRepr: TypeRepr, select: Select, defaults: Map[String, Expr[Object]]): List[Expr[Any]] =  
      val flatten = extractFlatten(field)
      val fieldTypeRepr = substituteTypeArgs(classTypeRepr, subsitituted = classTypeRepr.memberType(field))
      val typeSymbol = fieldTypeRepr.typeSymbol
      if (flatten) {
        if (isMap(fieldTypeRepr)) {
          val (keyTpe0, valueTpe0) = fieldTypeRepr.typeArgs match {
            case key :: value :: Nil => (key, value) 
            case _ => report.errorAndAbort(s"Unsupported type ${typeSymbol} for flattening", v.asTerm.pos)
          }
          val writerTpe0 = TypeRepr.of[W].appliedTo(valueTpe0)
          (keyTpe0.asType, valueTpe0.asType, writerTpe0.asType) match {
            case ('[keyTpe], '[valueTpe], '[writerTpe])=>
              val snippet = '{
                ${select.asExprOf[Map[keyTpe, valueTpe]]}.foreach { (k, v) =>
                  ${self}.writeSnippetMappedName[R, valueTpe](
                    ${ctx},
                    k.toString,
                    summonInline[writerTpe],
                    v,
                  )
                }
              }
              List(snippet)
          }
        }
        else if (isCaseClass(typeSymbol)) {
          typeSymbol.typeRef.dealias.asType match {
            case '[t] =>
              fieldLabelsImpl0[t]
                .flatMap { case (rawLabel, label) =>
                  val newDefaults = getDefaultParamsImpl0[t]
                  val newSelect = Select.unique(select, rawLabel.name)
                  val newClassTypeRepr = TypeRepr.of[T]
                  loop(rawLabel, label, newClassTypeRepr, newSelect, newDefaults)
                }
            case _ =>
              report.errorAndAbort("Unsupported type for flattening", v)
          }
        } else report.errorAndAbort(s"${typeSymbol} is not a case class or a immutable.Map", v.asTerm.pos)
      }
      else {
        val tpe0 = fieldTypeRepr
        val writerTpe0 = TypeRepr.of[W].appliedTo(tpe0)
        (tpe0.asType, writerTpe0.asType) match
          case ('[tpe], '[writerTpe]) =>
            val snippet = '{
              ${self}.writeSnippetMappedName[R, tpe](
                ${ctx},
                ${thisOuter}.objectAttributeKeyWriteMap(${Expr(label)}),
                summonInline[writerTpe],
                ${select.asExprOf[Any]},
              )
            }
            List(
              if (!defaults.contains(label)) snippet
              else {
                val serDflt = serDfltVals(thisOuter, field, classTypeRepr.typeSymbol)
                '{if ($serDflt || ${select.asExprOf[Any]} != ${defaults(label)}) $snippet}
              }
            )
      }

  Expr.block(
    fieldLabelsImpl0[T]
      .flatMap { (rawLabel, label) =>
        val defaults = getDefaultParamsImpl0[T]
        val select = Select.unique(v.asTerm, rawLabel.name)
        val classTypeRepr = TypeRepr.of[T]
        loop(rawLabel, label, classTypeRepr, select, defaults)
      },
    '{()}
  )

private def sealedHierarchyParents[T](using Quotes, Type[T]): List[quotes.reflect.Symbol] =
  import quotes.reflect._

  TypeRepr.of[T].baseClasses.filter(_.flags.is(Flags.Sealed))

inline def isMemberOfSealedHierarchy[T]: Boolean = ${ isMemberOfSealedHierarchyImpl[T] }
def isMemberOfSealedHierarchyImpl[T](using Quotes, Type[T]): Expr[Boolean] =
  Expr(sealedHierarchyParents[T].nonEmpty)

inline def tagKey[T](inline thisOuter: upickle.core.Types with upickle.implicits.MacrosCommon): String = ${ tagKeyImpl[T]('thisOuter) }
def tagKeyImpl[T](using Quotes, Type[T])(thisOuter: Expr[upickle.core.Types with upickle.implicits.MacrosCommon]): Expr[String] =
  import quotes.reflect._

  // `case object`s extend from `Mirror`, which is `sealed` and will never have a `@key` annotation
  // so we need to filter it out to ensure it doesn't trigger an error in `tagKeyFromParents`
  val mirrorType = Symbol.requiredClass("scala.deriving.Mirror")
  MacrosCommon.tagKeyFromParents(
    Type.show[T],
    sealedHierarchyParents[T].filterNot(_ == mirrorType),
    extractKey,
    (_: Symbol).name,
    report.errorAndAbort,
  ) match{
    case Some(v) => Expr(v)
    case None => '{${thisOuter}.tagName}
  }

def substituteTypeArgs(using Quotes)(tpe: quotes.reflect.TypeRepr, subsitituted: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr = {
  import quotes.reflect._
  val constructorSym = tpe.typeSymbol.primaryConstructor
  val constructorParamSymss = constructorSym.paramSymss

  val tparams0 = constructorParamSymss.flatten.filter(_.isType)
  subsitituted.substituteTypes(tparams0 ,tpe.typeArgs)
}

inline def applyConstructor[T](params: Array[Any], map: scala.collection.mutable.Map[String, Any]): T = ${ applyConstructorImpl[T]('params, 'map) }
def applyConstructorImpl[T](using quotes: Quotes, t0: Type[T])(params: Expr[Array[Any]], map: Expr[scala.collection.mutable.Map[String, Any]]): Expr[T] =
  import quotes.reflect._
  def apply(tpe: TypeRepr, typeArgs: List[TypeRepr], offset: Int): (Term, Int) = {
    val companion: Symbol = tpe.classSymbol.get.companionModule
    val constructorSym = tpe.typeSymbol.primaryConstructor
    val constructorParamSymss = constructorSym.paramSymss

    val (tparams0, params0) = constructorParamSymss.flatten.partition(_.isType)
    val constructorTpe = tpe.memberType(constructorSym).widen

    val (rhs, nextOffset) = params0.foldLeft((List.empty[Term], offset)) { case ((terms, i), sym0) =>
        val tpe0 = constructorTpe.memberType(sym0)
        val appliedTpe = tpe0.substituteTypes(tparams0, typeArgs)
        val typeSymbol = appliedTpe.typeSymbol
        val flatten = extractFlatten(sym0)
        if (flatten) {
          if (isMap(appliedTpe)) {
            val keyTpe0 = appliedTpe.typeArgs.head
            val valueTpe0 = appliedTpe.typeArgs(1)
            (keyTpe0.asType, valueTpe0.asType) match {
              case ('[keyTpe], '[valueTpe]) =>
                val typedMap =  '{${map}.asInstanceOf[collection.mutable.Map[keyTpe, valueTpe]]}.asTerm
                val term = Select.unique(typedMap, "toMap")
                (term :: terms, i)
            }
          }
          else if (isCaseClass(typeSymbol)) {
            typeSymbol.typeRef.dealias.asType match {
              case '[t] =>
                val newTpe = TypeRepr.of[t]
                val (term, nextOffset) = newTpe match {
                  case t: AppliedType => apply(newTpe, t.args, i)
                  case t: TypeRef => apply(newTpe, List.empty, i)
                  case t: TermRef => (Ref(t.classSymbol.get.companionModule), i)
                }
                (term :: terms, nextOffset)
              case _ =>
                report.errorAndAbort(s"Unsupported type $typeSymbol for flattening")
            }
          } else report.errorAndAbort(s"${typeSymbol} is not a case class or a immutable.Map")
        }
        else {
          val lhs = '{$params(${ Expr(i) })}
          val term = appliedTpe match {
            case AnnotatedType(AppliedType(base, Seq(arg)), x) if x.tpe =:= defn.RepeatedAnnot.typeRef =>
              arg.asType match {
                case '[t] =>
                  Typed(
                    lhs.asTerm,
                    TypeTree.of(using AppliedType(defn.RepeatedParamClass.typeRef, List(arg)).asType)
                  )
              }
            case tpe =>
              tpe.asType match {
                case '[t] => '{ $lhs.asInstanceOf[t] }.asTerm
              }
          }
          (term :: terms, i + 1)
        }
    }

    (Select.overloaded(Ref(companion), "apply", typeArgs, rhs.reverse), nextOffset)
  }

  val tpe = TypeRepr.of[T]
  tpe match{
    case t: AppliedType => apply(tpe, t.args, 0)._1.asExprOf[T]
    case t: TypeRef => apply(tpe, List.empty, 0)._1.asExprOf[T]
    case t: TermRef => '{${Ref(t.classSymbol.get.companionModule).asExprOf[Any]}.asInstanceOf[T]}
  }

inline def tagName[T]: String = ${ tagNameImpl[T] }
def tagNameImpl[T](using Quotes, Type[T]): Expr[String] =
  tagNameImpl0(identity)

def tagNameImpl0[T](transform: String => String)(using Quotes, Type[T]): Expr[String] =
  import quotes.reflect._

  val sym = TypeTree.of[T].symbol

  Expr(
    extractKey(sym) match
    case Some(name) => name
    case None =>
      // In Scala 3 enums, we use the short name of each case as the tag, rather
      // than the fully-qualified name. We can do this because we know that all
      // enum cases are in the same `enum Foo` namespace with distinct short names,
      // whereas sealed trait instances could be all over the place with identical
      // short names only distinguishable by their prefix.
      //
      // Harmonizing these two cases further is TBD
      if (TypeRepr.of[T] <:< TypeRepr.of[scala.reflect.Enum]) {
        // Sometimes .symbol/.typeSymbol gives the wrong thing:
        //
        // - `.symbol.name` returns `<none>` for `LinkedList.Node[T]`
        // - `.typeSymbol` returns `LinkedList` for `LinkedList.End`
        //
        // so we just mangle `.show` even though it's super gross
        TypeRepr.of[T] match{
          case TermRef(prefix, value) => value
          case TypeRef(prefix, value) => value
          case AppliedType(TermRef(prefix, value), _) => value
          case AppliedType(TypeRef(prefix, value), _) => value
        }
      } else {
        transform(TypeTree.of[T].tpe.typeSymbol.fullName.filter(_ != '$'))
      }
  )
inline def shortTagName[T]: String = ${ shortTagNameImpl[T] }
def shortTagNameImpl[T](using Quotes, Type[T]): Expr[String] =
  import quotes.reflect._
  val sealedClassSymbol = if (TypeRepr.of[T].baseClasses.contains(TypeRepr.of[T].typeSymbol))
    Some(TypeRepr.of[T].typeSymbol.fullName.split('.'))
  else None
  val segments = TypeRepr.of[T].baseClasses
    .filter(_.flags.is(Flags.Sealed))
    .flatMap(_.children)
    .filter(_.flags.is(Flags.Case))
    .map(_.fullName.split('.')) ++
    sealedClassSymbol.toList

  val identicalSegmentCount = Range(0, segments.map(_.length).max - 1)
    .takeWhile(i => segments.map(_.lift(i)).distinct.size == 1)
    .length

  tagNameImpl0(_.split('.').drop(identicalSegmentCount).mkString("."))

inline def isSingleton[T]: Boolean = ${ isSingletonImpl[T] }
def isSingletonImpl[T](using Quotes, Type[T]): Expr[Boolean] =
  import quotes.reflect._
  Expr(TypeRepr.of[T].typeSymbol.flags.is(Flags.Module) || TypeRepr.of[T].isSingleton)

inline def getSingleton[T]: T = ${ getSingletonImpl[T] }
def getSingletonImpl[T](using Quotes, Type[T]): Expr[T] =
  import quotes.reflect._

  TypeRepr.of[T] match{
    case tref: TypeRef => Ref(tref.classSymbol.get.companionModule).asExpr.asInstanceOf[Expr[T]]
    case v => '{valueOf[T]}
  }


inline def defineEnumReaders[T0, T <: Tuple](prefix: Any): T0 = ${ defineEnumVisitorsImpl[T0, T]('prefix, "macroR") }
inline def defineEnumWriters[T0, T <: Tuple](prefix: Any): T0 = ${ defineEnumVisitorsImpl[T0, T]('prefix, "macroW") }
def defineEnumVisitorsImpl[T0, T <: Tuple](prefix: Expr[Any], macroX: String)(using Quotes, Type[T0], Type[T]): Expr[T0] =
  import quotes.reflect._

  def handleType(tpe: TypeRepr, name: String, skipTrait: Boolean): Option[(ValDef, Symbol)] = {

    val AppliedType(typePrefix, List(arg)) = tpe: @unchecked

    if (skipTrait &&
        (arg.typeSymbol.flags.is(Flags.Trait) ||
          // Filter out `enum`s, because the `case`s of an enum are flagged as
          // abstract enums for some reasons rather than as case classes
          (arg.typeSymbol.flags.is(Flags.Abstract) && !arg.typeSymbol.flags.is(Flags.Enum)))){
      None
    } else {
      val sym = Symbol.newVal(
        Symbol.spliceOwner,
        name,
        tpe,
        Flags.Implicit | Flags.Lazy,
        Symbol.noSymbol
      )

      val macroCall = TypeApply(
        Select(prefix.asTerm, prefix.asTerm.tpe.typeSymbol.methodMember(macroX).head),
        List(TypeTree.of(using arg.asType))
      )

      val newDef = ValDef(sym, Some(macroCall))

      Some((newDef, sym))
    }
  }

  def getDefs(t: TypeRepr, defs: List[(ValDef, Symbol)]): List[(ValDef, Symbol)] = {
    t match{
      case AppliedType(prefix, args) =>
        val defAndSymbol = handleType(args(0), "x" + defs.size, skipTrait = true)
        getDefs(args(1), defAndSymbol.toList ::: defs)
      case _ if t =:= TypeRepr.of[EmptyTuple] => defs
    }
  }
  val subTypeDefs = getDefs(TypeRepr.of[T], Nil)
  val topTraitDefs = handleType(TypeRepr.of[T0], "x" + subTypeDefs.size, skipTrait = false)
  val allDefs = topTraitDefs.toList ::: subTypeDefs

  Block(allDefs.map(_._1), Ident(allDefs.head._2.termRef)).asExprOf[T0]

inline def validateFlattenAnnotation[T](): Unit = ${ validateFlattenAnnotationImpl[T] }
def validateFlattenAnnotationImpl[T](using Quotes, Type[T]): Expr[Unit] =
  import quotes.reflect._
  val fields = allFields[T]
  if (fields.count(_._5) > 1) {
    report.errorAndAbort("Only one Map can be annotated with @upickle.implicits.flatten in the same level")
  }
  if (fields.map(_._2).distinct.length != fields.length) {
    report.errorAndAbort("There are multiple fields with the same key")
  }
  if (fields.exists {case (_, _, tpe, _, isFlattenMap) => isFlattenMap && !(tpe.typeArgs.head.dealias =:= TypeRepr.of[String].dealias)}) {
    report.errorAndAbort("The key type of a Map annotated with @flatten must be String.")
  }
  '{()}

private def isMap(using Quotes)(tpe: quotes.reflect.TypeRepr): Boolean = {
  import quotes.reflect._
  tpe.typeSymbol == TypeRepr.of[collection.immutable.Map[_, _]].typeSymbol
}

private def isCaseClass(using Quotes)(typeSymbol: quotes.reflect.Symbol): Boolean = {
  import quotes.reflect._
  typeSymbol.isClassDef && typeSymbol.flags.is(Flags.Case)
}
