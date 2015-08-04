/*
 * Copyright (c) 2013-15 Miles Sabin
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless

import scala.annotation.tailrec
import scala.language.experimental.macros
import scala.language.reflectiveCalls

import scala.collection.immutable.ListMap
import scala.reflect.macros.Context

trait Lazy[+T] extends Serializable {
  val value: T

  def map[U](f: T => U): Lazy[U] = Lazy { f(value) }
  def flatMap[U](f: T => Lazy[U]): Lazy[U] = Lazy { f(value).value }
}

object Lazy {
  implicit def apply[T](t: => T): Lazy[T] =
    new Lazy[T] {
      lazy val value = t
    }

  def unapply[T](lt: Lazy[T]): Option[T] = Some(lt.value)

  class Values[T <: HList](val values: T) extends Serializable
  object Values {
    implicit val hnilValues: Values[HNil] = new Values(HNil)
    implicit def hconsValues[H, T <: HList](implicit lh: Lazy[H], t: Values[T]): Values[H :: T] =
      new Values(lh.value :: t.values)
  }

  def values[T <: HList](implicit lv: Lazy[Values[T]]): T = lv.value.values

  implicit def mkLazy[I]: Lazy[I] = macro LazyMacros.mkLazyImpl[I]

  trait Cached[+T] extends Lazy[T] {
    override def map[U](f: T => U): Cached[U] = Cached { f(value) }
    def flatMap[U](f: T => Cached[U]): Cached[U] = Cached { f(value).value }
  }

  object Cached {
    implicit def apply[T](t: => T): Cached[T] =
      new Cached[T] {
        val value = t
      }

    def unapply[T](lt: Cached[T]): Option[T] = Some(lt.value)

    implicit def mkCached[I]: Cached[I] = macro LazyMacros.mkCachedLazyImpl[I]
  }

}

object lazily {
  def apply[T](implicit lv: Lazy[T]): T = lv.value
}

trait Strict[+T] extends Serializable {
  val value: T

  def map[U](f: T => U): Strict[U] = Strict { f(value) }
  def flatMap[U](f: T => Strict[U]): Strict[U] = Strict { f(value).value }
}

object Strict {
  implicit def apply[T](t: T): Strict[T] =
    new Strict[T] {
      val value = t
    }

  def unapply[T](lt: Strict[T]): Option[T] = Some(lt.value)

  implicit def mkStrict[I]: Strict[I] = macro LazyMacros.mkStrictImpl[I]

  trait Cached[+T] extends Strict[T] {
    override def map[U](f: T => U): Cached[U] = Cached { f(value) }
    def flatMap[U](f: T => Cached[U]): Cached[U] = Cached { f(value).value }
  }

  object Cached {
    implicit def apply[T](t: T): Cached[T] =
      new Cached[T] {
        val value = t
      }

    def unapply[T](lt: Cached[T]): Option[T] = Some(lt.value)

    implicit def mkCached[I]: Cached[I] = macro LazyMacros.mkCachedStrictImpl[I]
  }

}

class LazyMacros[C <: Context](val c: C) {
  import c.universe._

  def mkLazyImpl[I](implicit iTag: WeakTypeTag[I]): Tree =
    mkImpl[I](
      (tree, actualType) => q"_root_.shapeless.Lazy.apply[$actualType]($tree)",
      q"null.asInstanceOf[_root_.shapeless.Lazy[Nothing]]",
      None
    )

  def mkStrictImpl[I](implicit iTag: WeakTypeTag[I]): Tree =
    mkImpl[I](
      (tree, actualType) => q"_root_.shapeless.Strict.apply[$actualType]($tree)",
      q"null.asInstanceOf[_root_.shapeless.Strict[Nothing]]",
      None
    )

  def mkCachedLazyImpl[I](implicit iTag: WeakTypeTag[I]): Tree =
    mkImpl[I](
      (tree, actualType) => q"_root_.shapeless.Lazy.Cached.apply[$actualType]($tree)",
      q"null.asInstanceOf[_root_.shapeless.Lazy.Cached[Nothing]]",
      Some("")
    )

  def mkCachedStrictImpl[I](implicit iTag: WeakTypeTag[I]): Tree =
    mkImpl[I](
      (tree, actualType) => q"_root_.shapeless.Strict.Cached.apply[$actualType]($tree)",
      q"null.asInstanceOf[_root_.shapeless.Strict.Cached[Nothing]]",
      Some("")
    )

  def mkImpl[I](mkInst: (c.Tree, c.Type) => c.Tree, nullInst: => c.Tree, cacheOpt: Option[String])(implicit iTag: WeakTypeTag[I]): Tree = {
    (c.openImplicits.headOption, iTag.tpe.normalize) match {
      case (Some((TypeRef(_, _, List(tpe)), _)), _) =>
        LazyMacros.deriveInstance(c)(tpe.map(_.normalize), mkInst, cacheOpt)
      case (None, tpe) if tpe.typeSymbol.isParameter =>       // Workaround for presentation compiler
        nullInst
      case (None, tpe) =>                                     // Non-implicit invocation
        LazyMacros.deriveInstance(c)(tpe, mkInst, cacheOpt)
      case _ =>
        c.abort(c.enclosingPosition, s"Bad Lazy materialization ${c.openImplicits.head}")
    }
  }
}

object LazyMacros {
  def inst(c: Context) = new LazyMacros[c.type](c)

  def mkLazyImpl[I: c.WeakTypeTag](c: Context): c.Expr[Lazy[I]] = {
    import c.universe._

    mkImpl[I, Lazy](c)(
      c.Expr[Lazy[I]](inst(c).mkLazyImpl[I]),
      lm =>
        lm.asInstanceOf[
          { def mkLazyImpl(c: Context)(i: c.WeakTypeTag[I]): c.Expr[Lazy[I]] }
        ].mkLazyImpl(c)(weakTypeTag[I])
    )
  }

  def mkStrictImpl[I: c.WeakTypeTag](c: Context): c.Expr[Strict[I]] = {
    import c.universe._

    mkImpl[I, Strict](c)(
      c.Expr[Strict[I]](inst(c).mkStrictImpl[I]),
      lm =>
        lm.asInstanceOf[
          { def mkStrictImpl(c: Context)(i: c.WeakTypeTag[I]): c.Expr[Strict[I]] }
        ].mkStrictImpl(c)(weakTypeTag[I])
    )
  }

  def mkCachedLazyImpl[I: c.WeakTypeTag](c: Context): c.Expr[Lazy.Cached[I]] = {
    import c.universe._

    mkImpl[I, Lazy.Cached](c)(
      c.Expr[Lazy.Cached[I]](inst(c).mkCachedLazyImpl[I]),
      lm =>
        lm.asInstanceOf[
          { def mkCachedLazyImpl(c: Context)(i: c.WeakTypeTag[I]): c.Expr[Lazy.Cached[I]] }
        ].mkCachedLazyImpl(c)(weakTypeTag[I])
    )
  }

  def mkCachedStrictImpl[I: c.WeakTypeTag](c: Context): c.Expr[Strict.Cached[I]] = {
    import c.universe._

    mkImpl[I, Strict.Cached](c)(
      c.Expr[Strict.Cached[I]](inst(c).mkCachedStrictImpl[I]),
      lm =>
        lm.asInstanceOf[
          { def mkCachedStrictImpl(c: Context)(i: c.WeakTypeTag[I]): c.Expr[Strict.Cached[I]] }
        ].mkCachedStrictImpl(c)(weakTypeTag[I])
    )
  }

  def mkImpl[I: c.WeakTypeTag, L[I]](c: Context)(
    f: => c.Expr[L[I]],
    f0: Any => c.Expr[L[I]]
  ): c.Expr[L[I]] = {
    import c.universe._

    val lmSym = typeOf[LazyMacros.type].typeSymbol
    lmSym.attachments.all.headOption match {
      case Some(lm) =>
        if(lm == LazyMacros)
          f
        else
          f0(lm)
      case None =>
        lmSym.updateAttachment[LazyMacros.type](this)
        try {
          f
        } finally {
            lmSym.removeAttachment[LazyMacros.type]
        }
    }
  }

  var caches = Map.empty[String, List[(Any, Any)]]

  var dcRef: Option[DerivationContext] = None

  object Debug {
    var startTime = 0L
    var count = 0
    var verbose = false

    def enable(): Unit = macro enableImpl
    def enableImpl(c: Context)(): c.Expr[Unit] = {
      import c.universe._
      verbose = true
      c.Expr(q"()")
    }
  }

  def deriveInstance(c: Context)(tpe: c.Type, mkInst: (c.Tree, c.Type) => c.Tree, cacheOpt: Option[String]): c.Tree = {
    val cached =
      if (dcRef.isEmpty)
        cacheOpt.flatMap(caches.get).flatMap { cache =>
          cache.collectFirst {
            case (tpe0, v) if tpe0.asInstanceOf[c.Type] =:= tpe =>
              val res = v.asInstanceOf[c.Tree]
              if (Debug.verbose)
                println(s"Cache hit ($cacheOpt): $tpe")
              res
          }
        }
      else
        None

    def derive: c.Tree = {
      val (dc, root) =
        dcRef match {
          case None =>
            val dc = DerivationContext(c)
            dcRef = Some(dc)
            (dc, true)
          case Some(dc) =>
            (DerivationContext.establish(dc, c), false)
        }

      if (Debug.verbose && root) {
        if (Debug.startTime == 0L)
          Debug.startTime = System.currentTimeMillis()
        Debug.count += 1
        println(s"Deriving $tpe ${Seq(Debug.count.toString, ((System.currentTimeMillis() - Debug.startTime) / 1000.0).toString).mkString("(", ", ", ")")}")
      }

      if (Debug.verbose)
        println(s"Deriving $tpe")

      if (root)
        // Sometimes corrupted, and slows things too
        c.universe.asInstanceOf[scala.tools.nsc.Global].analyzer.resetImplicits()

      try {
        val res =
        dc.State.deriveInstance(tpe, root, mkInst)
        if (Debug.verbose)
          println(s"Derived $tpe:\n  $res")
        res
      } finally {
        if(root) dcRef = None
      }
    }

    cached.getOrElse{
      if (Debug.verbose && dcRef.isEmpty)
        println(s"Cache miss ($cacheOpt): $tpe")
      val res = derive
      if (dcRef.isEmpty)
        for (cache <- cacheOpt)
          LazyMacros.caches += cache -> ((tpe, res) :: LazyMacros.caches.getOrElse(cache, Nil))
      res
    }
  }
}

object DerivationContext {
  type Aux[C0] = DerivationContext { type C = C0 }

  def apply(c0: Context): Aux[c0.type] =
    new DerivationContext {
      type C = c0.type
      val c: C = c0
    }

  def establish(dc: DerivationContext, c0: Context): Aux[c0.type] =
    dc.asInstanceOf[DerivationContext { type C = c0.type }]
}

trait LazyExtension {
  type Ctx <: DerivationContext
  val ctx: Ctx

  import ctx._
  import c.universe._

  def id: String

  type ThisState

  def initialState: ThisState

  def derive(
    state0: State,
    extState: ThisState,
    update: (State, ThisState) => State )(
    instTpe0: Type
  ): Option[Either[String, (State, Instance)]]
}

trait LazyExtensionCompanion {
  def instantiate(ctx0: DerivationContext): LazyExtension { type Ctx = ctx0.type }

  def initImpl(c: Context): Nothing = {
    val ctx = LazyMacros.dcRef.getOrElse(
      c.abort(c.enclosingPosition, "")
    )

    val extension = instantiate(ctx)
    ctx.State.addExtension(extension)

    c.abort(c.enclosingPosition, s"Added extension ${extension.id}")
  }
}

trait LazyDefinitions {
  type C <: Context
  val c: C

  import c.universe._

  case class Instance(
    instTpe: Type,
    name: TermName,
    symbol: Symbol,
    inst: Option[Tree],
    actualTpe: Type,
    dependsOn: List[Type]
  ) {
    def ident = Ident(symbol)
  }

  object Instance {
    def apply(instTpe: Type) = {
      val nme = newTermName(c.fresh("inst"))
      val sym = NoSymbol.newTermSymbol(nme).setTypeSignature(instTpe)

      new Instance(instTpe, nme, sym, None, instTpe, Nil)
    }
  }

  class TypeWrapper(val tpe: Type) {
    override def equals(other: Any): Boolean =
      other match {
        case TypeWrapper(tpe0) => tpe =:= tpe0
        case _ => false
      }
    override def toString = tpe.toString
  }

  object TypeWrapper {
    def apply(tpe: Type) = new TypeWrapper(tpe)
    def unapply(tw: TypeWrapper): Option[Type] = Some(tw.tpe)
  }


  case class ExtensionWithState[S <: DerivationContext, T](
    extension: LazyExtension { type Ctx = S; type ThisState = T },
    state: T
  ) {
    import extension.ctx

    def derive(
      state0: ctx.State,
      update: (ctx.State, ExtensionWithState[S, T]) => ctx.State )(
      instTpe0: ctx.c.Type
    ): Option[Either[String, (ctx.State, ctx.Instance)]] =
      extension.derive(state0, state, (ctx, t) => update(ctx, copy(state = t)))(instTpe0)
  }

  object ExtensionWithState {
    def apply(extension: LazyExtension): ExtensionWithState[extension.Ctx, extension.ThisState] =
      ExtensionWithState(extension, extension.initialState)
  }

}

trait DerivationContext extends shapeless.CaseClassMacros with LazyDefinitions { ctx =>
  type C <: Context
  val c: C

  import c.universe._

  object State {
    final val ctx0: ctx.type = ctx
    val empty = State("", ListMap.empty, Nil, Nil)

    private var current = Option.empty[State]
    private var addExtensions = List.empty[ExtensionWithState[ctx.type, _]]

    def addExtension(extension: LazyExtension { type Ctx = ctx0.type }): Unit = {
      addExtensions = ExtensionWithState(extension) :: addExtensions
    }

    def takeNewExtensions(): List[ExtensionWithState[ctx.type, _]] = {
      val addExtensions0 = addExtensions
      addExtensions = Nil
      addExtensions0
    }

    def resolveInstance(state: State)(tpe: Type): Option[(State, Tree)] = {
      val former = State.current
      State.current = Some(state)
      val (state0, tree) =
        try {
          val tree = c.inferImplicitValue(tpe, silent = true)
          (State.current.get, tree)
        } finally {
          State.current = former
        }

        if (tree == EmptyTree || addExtensions.nonEmpty) None
        else Some((state0, tree))
      }

    def deriveInstance(instTpe0: Type, root: Boolean, mkInst: (Tree, Type) => Tree): Tree = {
      if (root) {
        assert(current.isEmpty)
        val open = c.openImplicits
        val name = "lazy"
        current = Some(empty.copy(name = name))
      }

      ctx.derive(current.get)(instTpe0) match {
        case Right((state, inst)) =>
          val (tree, actualType) = if (root) mkInstances(state)(instTpe0) else (inst.ident, inst.actualTpe)
          current = if (root) None else Some(state)
          mkInst(tree, actualType)
        case Left(err) =>
          abort(err)
      }
    }
  }

  case class State(
    name: String,
    dict: ListMap[TypeWrapper, Instance],
    open: List[Instance],
    extensions: List[ExtensionWithState[ctx.type, _]]
  ) {
    def addDependency(tpe: Type): State = {
      import scala.::
      val open0 = open match {
        case Nil => Nil
        case h :: t => h.copy(dependsOn = if (h.instTpe =:= tpe || h.dependsOn.exists(_ =:= tpe)) h.dependsOn else tpe :: h.dependsOn) :: t
      }
      copy(open = open0)
    }
    private def update(inst: Instance): State =
      copy(dict = dict.updated(TypeWrapper(inst.instTpe), inst))
    def openInst(tpe: Type): (State, Instance) = {
      val inst = Instance(tpe)
      val state0 = addDependency(tpe)
      if (LazyMacros.Debug.verbose)
        println(s"Opening $tpe")
      (state0.copy(open = inst :: state0.open).update(inst), inst)
    }

    def closeInst(tpe: Type, tree: Tree, actualTpe: Type): (State, Instance) = {
      assert(open.nonEmpty)
      assert(open.head.instTpe =:= tpe)
      val instance = open.head
      val sym = instance.symbol.setTypeSignature(actualTpe)
      val instance0 = instance.copy(inst = Some(tree), actualTpe = actualTpe, symbol = sym)
      if (LazyMacros.Debug.verbose)
        println(s"Closing $tpe")
      (copy(open = open.tail).update(instance0), instance0)
    }

    def lookup(instTpe: Type): Either[State, (State, Instance)] =
      dict.get(TypeWrapper(instTpe)).map((this, _)) match {
        case Some((s, i)) => Right((s.addDependency(instTpe), i))
        case None => Left(openInst(instTpe)._1)
      }


    def dependsOn(tpe: Type): List[Instance] = {
      import scala.::
      def helper(tpes: List[List[Type]], acc: List[Instance]): List[Instance] =
        tpes match {
          case Nil => acc
          case Nil :: t =>
            helper(t, acc)
          case (h :: t0) :: t =>
            if (acc.exists(_.instTpe =:= h))
              helper(t0 :: t, acc)
            else {
              val inst = dict(TypeWrapper(h))
              helper(inst.dependsOn :: t0 :: t, inst :: acc)
            }
        }

      helper(List(List(tpe)), Nil)
    }
  }

  def stripRefinements(tpe: Type): Option[Type] =
    tpe match {
      case RefinedType(parents, decls) => Some(parents.head)
      case _ => None
    }

  def resolve(state0: State)(inst: Instance): Option[(State, Instance)] =
    resolve0(state0)(inst.instTpe)
      .filter{case (_, tree, _) => !tree.equalsStructure(inst.ident) }
      .map {case (state1, extInst, actualTpe) =>
        state1.closeInst(inst.instTpe, extInst, actualTpe)
      }

  def resolve0(state0: State)(instTpe: Type): Option[(State, Tree, Type)] = {
    val extInstOpt =
      State.resolveInstance(state0)(instTpe)
        .orElse(
          stripRefinements(instTpe).flatMap(State.resolveInstance(state0))
        )

    extInstOpt.map {case (state1, extInst) =>
      (state1, extInst, extInst.tpe match {
        case NullaryMethodType(restpe) => restpe
        case other => other
      })
    }
  }

  def derive(state0: State)(instTpe0: Type): Either[String, (State, Instance)] = {
    val fromExtensions: Option[Either[String, (State, Instance)]] =
      state0.extensions.zipWithIndex.foldRight(Option.empty[Either[String, (State, Instance)]]) {
        case (_, acc @ Some(_)) => acc
        case ((ext, idx), None) =>
          def update(state: State, withState: ExtensionWithState[ctx.type, _]) =
            state.copy(extensions = state.extensions.updated(idx, withState))

          ext.derive(state0, update)(instTpe0)
      }

    val result: Either[String, (State, Instance)] =
      fromExtensions.getOrElse {
        state0.lookup(instTpe0).left.flatMap { state =>
          val inst = state.dict(TypeWrapper(instTpe0))
          resolve(state)(inst)
            .toRight(s"Unable to derive $instTpe0")
        }
      }

    // Check for newly added extensions, and re-derive with them.
    lazy val current = state0.extensions.map(_.extension.id).toSet
    val newExtensions0 = State.takeNewExtensions().filter(ext => !current(ext.extension.id))
    if (newExtensions0.nonEmpty)
      derive(state0.copy(extensions = newExtensions0 ::: state0.extensions))(instTpe0)
    else
      result
  }

  // Workaround for https://issues.scala-lang.org/browse/SI-5465
  class StripUnApplyNodes extends Transformer {
    val global = c.universe.asInstanceOf[scala.tools.nsc.Global]
    import global.nme

    override def transform(tree: Tree): Tree = {
      super.transform {
        tree match {
          case UnApply(Apply(Select(qual, nme.unapply | nme.unapplySeq), List(Ident(nme.SELECTOR_DUMMY))), args) =>
            Apply(transform(qual), transformTrees(args))
          case t => t
        }
      }
    }
  }

  class Inliner(sym: Name, inlined: Tree) extends Transformer {
    var count = 0

    override def transform(tree: Tree): Tree =
      super.transform {
        tree match {
          case Ident(sym0) if sym0 == sym =>
            count += 1
            inlined
          case t => t
        }
      }
  }

  object Instances {
    // These seem not to be dealiased as expected (try with Functor[Some] from the examples),
    // and are not inlined correctly.
    def hasHKAliases(tpe: Type) =
      tpe match {
        case TypeRef(_, _, args0) =>
          args0.map(_.normalize).exists {
            case PolyType(args, pt) =>
              true
            case _ => false
          }
        case _ => false
      }

    def canBeInlined(t: (Instance, List[String])): Boolean = {
      val (inst, dependees) = t
      inst.dependsOn.isEmpty && dependees.lengthCompare(1) == 0
    }

    def priorityCanBeSubstituted(t: (Instance, List[String])): Option[Tree] = {
      val (inst, _) = t
      if (inst.dependsOn.nonEmpty)
        None
      else
        inst.inst.get match {
          case q"$method[..$tp](shapeless.Strict.apply[..$tpa](_root_.shapeless.Priority.High[..${List(tph: TypeTree)}]($something)))"
            if tph.tpe =:= inst.actualTpe => Some(something)
          case other =>
            None
        }
    }

    def apply(state: State, primaryTpe: Type): Instances = {
      val instances = state.dependsOn(primaryTpe)
      var m = Map.empty[String, List[String]]

      for (inst <- instances) {
        val name = inst.name.toString

        for (depTpe <- inst.dependsOn) {
          val depInst = state.dict(TypeWrapper(depTpe))
          val depName = depInst.name.toString
          m += depName -> (name :: m.getOrElse(depName, Nil))
        }
      }

      Instances(
        instances.map(inst => inst.name.toString -> ((inst, m.getOrElse(inst.name.toString, Nil), !hasHKAliases(inst.instTpe)))).toMap,
        state.dict(TypeWrapper(primaryTpe)).name.toString
      )
    }
  }

  case class Instances(
    dict: Map[String, (Instance, List[String], Boolean)],
    root: String
  ) {
    import Instances._

    def prioritySubstitute: Option[Instances] =
      dict.iterator
        .map{case (k, v @ (inst, deps, canBeInlined)) => (k, v, priorityCanBeSubstituted((inst, deps)))}
        .collectFirst { case (k, (inst, dependees, canBeInlined), Some(tree)) =>
          copy(dict = dict.updated(k, (inst.copy(inst = Some(tree)), dependees, canBeInlined)))
        }

    def inline: Option[Instances] =
      dict.find{case (k, v @ (inst, deps, canBeInlined0)) => canBeInlined0 && k != root && canBeInlined((inst, deps)) } match {
        case None => None
        case Some((k, (inst, dependees, _))) =>
          assert(dependees.length == 1)
          val (dependeeInst, dependeeDependedOnBy, canBeInlined0) = dict(dependees.head)
          val inliner = new Inliner(inst.name, inst.inst.get)
          val dependeeInst0 = inliner.transform(dependeeInst.inst.get)

          val dict0 =
            if (inliner.count == 1) {
              if (LazyMacros.Debug.verbose)
                println(s"Inlined ${inst.instTpe}")
              (dict - k).updated(
                dependees.head,
                (
                  dependeeInst.copy(
                    dependsOn = dependeeInst.dependsOn.filterNot(_ =:= inst.instTpe),
                    inst = Some(dependeeInst0)
                  ),
                  dependeeDependedOnBy,
                  canBeInlined0
                )
              )
            } else
              dict.updated(k, (inst, dependees, false))

          Some(copy(dict = dict0))
      }

    @tailrec
    final def optimize: Instances =
      prioritySubstitute.orElse(inline) match {
        case None =>
          this
        case Some(instances) =>
          instances.optimize
      }
  }

  def mkInstances(state: State)(primaryTpe: Type): (Tree, Type) = {
    val instances0 = Instances(state, primaryTpe).optimize

    val instances = instances0.dict.toList.map(_._2._1)
    val (from, to) = instances.map { d => (d.symbol, NoSymbol) }.unzip

    def clean(inst: Tree) = {
      val cleanInst = c.resetLocalAttrs(inst.substituteSymbols(from, to))
      new StripUnApplyNodes().transform(cleanInst)
    }

    if (instances.length == 1) {
      val instance = instances.head
      import instance._
      inst match {
        case Some(inst) =>
          val cleanInst = clean(inst)
          (q"$cleanInst.asInstanceOf[$actualTpe]", actualTpe)
        case None =>
          abort(s"Uninitialized $instTpe lazy implicit")
      }
    } else {
      val instTrees =
        instances.map { instance =>
          import instance._
          inst match {
            case Some(inst) =>
              val cleanInst = clean(inst)
              q"""lazy val $name: $actualTpe = $cleanInst.asInstanceOf[$actualTpe]"""
            case None =>
              abort(s"Uninitialized $instTpe lazy implicit")
          }
        }

      val primaryInstance = state.lookup(primaryTpe).right.get._2
      val primaryNme = primaryInstance.name
      val clsName = newTypeName(c.fresh(state.name))

      val tree =
        q"""
          final class $clsName extends _root_.scala.Serializable {
            ..$instTrees
          }
          (new $clsName).$primaryNme
         """
      val actualType = primaryInstance.actualTpe

      (tree, actualType)
    }
  }
}
