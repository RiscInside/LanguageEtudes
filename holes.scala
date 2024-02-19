//> using scala 3
//> using dep org.scalatest::scalatest:3.2.18
//> using dep org.scalatest::scalatest-funsuite:3.2.18
//> using javaOpt -Xss10m

import org.scalatest.funsuite.AnyFunSuite
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer

final case class Meta(val id: Int, private var _solution: Option[Val]):
  final def solution = _solution
  final def solve(v: Val) = _solution = Some(v)

class MetaGenerator(private var lastId: Int = 0):
  private var allMetas: ArrayBuffer[Meta] = ArrayBuffer.empty

  final def apply(): Meta =
    val (newLastId, res) = (lastId + 1, new Meta(lastId, None))
    allMetas.addOne(res)
    lastId = newLastId
    res

  final def metas(): Vector[Meta] = allMetas.toVector

enum BD:
  case Bound, Defined

enum Term:
  case TVar(idx: Int)
  case TApp(fun: Term, arg: Term)
  case TAbs(name: String, body: Term)
  case TPi(name: String, ty: Term, body: Term)
  case TLet(name: String, ty: Term, is: Term, in: Term)
  case TU
  case TMeta(meta: Meta)
  case TInsertedMeta(meta: Meta, bds: Vector[BD])

  final def eval(env: Env = Vector.empty): Val = this match
    case TVar(idx)        => env(env.length - 1 - idx)
    case TApp(fun, arg)   => fun.eval(env)(arg.eval(env))
    case TAbs(name, body) => Val.VAbs(Closure(name, env, body))
    case TPi(name, ty, body) =>
      Val.VPi(ty.eval(env), Closure(name, env, body))
    case TLet(_, _, is, in)       => in.eval(env :+ is.eval(env))
    case TU                       => Val.VU
    case TMeta(meta)              => Val.meta(meta)
    case TInsertedMeta(meta, bds) => Val.meta(meta).applyBD(env, bds)

  final def nf(env: Env = Vector.empty): Term =
    this.eval(env).quote(env.length)

type Env = Vector[Val]

final case class Closure(val name: String, val env: Env, val tm: Term):
  final def apply(arg: Val): Val =
    tm.eval(env :+ arg)

enum Val:
  case VAbs(closure: Closure)
  case VPi(ty: Val, closure: Closure)
  case VU
  case VStuck(head: Head, spine: Spine)

  final def force(): Val = this match
    case VStuck(Head.HMeta(meta), spine) => {
      meta.solution.match
        case Some(solution) => solution(spine).force()
        case None           => this
    }
    case _ => this

  final def apply(arg: Val): Val = this match
    case VAbs(closure)       => closure(arg)
    case VStuck(head, spine) => VStuck(head, spine :+ Elim.EApp(arg))
    case _                   => ???

  final def elim(elim: Elim): Val = elim match
    case Elim.EApp(arg) => this(arg)

  /** Break down the spine after making progress on the head */
  @tailrec
  final def apply(spine: Spine): Val = (this, spine) match
    case (VStuck(head, leftSpine), rightSpine) =>
      VStuck(head, leftSpine ++ rightSpine)
    case (v, elim +: spine) => this.elim(elim)(spine)
    case (v, _)             => v

  /** Apply all bound variables from the environment */
  final def applyBD(env: Env, bds: Vector[BD]): Val =
    env.reverseIterator
      .zip(bds.reverseIterator)
      .filter(_._2 == BD.Bound)
      .map(_._1)
      .foldLeft(this)(_(_))

  final def quote(envSize: Int = 0): Term = this.force() match
    case VAbs(closure) =>
      Term.TAbs(
        closure.name,
        closure(Val.bound(envSize)).quote(envSize + 1)
      )
    case VPi(ty, closure) =>
      Term.TPi(
        closure.name,
        ty.quote(envSize),
        closure.apply(Val.bound(envSize)).quote(envSize + 1)
      )
    case VStuck(head, spine) =>
      val quotedHead = head match
        case Head.HMeta(meta)       => Term.TMeta(meta)
        case Head.HNeutral(neutral) => Term.TVar(envSize - 1 - neutral)

      spine.foldLeft(quotedHead)((head, elim) =>
        elim match
          case Elim.EApp(arg) => Term.TApp(head, arg.quote(envSize))
      )
    case VU => Term.TU

object Val:
  final def meta(meta: Meta): Val = VStuck(Head.HMeta(meta), Vector.empty)
  final def bound(lvl: Int): Val = VStuck(Head.HNeutral(lvl), Vector.empty)

enum Head:
  case HNeutral(lvl: Int)
  case HMeta(meta: Meta)

type Spine = Vector[Elim]

enum Elim:
  case EApp(arg: Val)

class TermBuilder(private val builder: (Int, MetaGenerator) => Term):
  final def build(): Term = builder(0, MetaGenerator())
  final def apply(args: TermBuilder*): TermBuilder =
    TermBuilder { (lvl: Int, metaGen: MetaGenerator) =>
      args.foldLeft(this.builder(lvl, metaGen))((fun, arg) =>
        Term.TApp(fun, arg.builder(lvl, metaGen))
      )
    }

  final def ->:(arg: TermBuilder): TermBuilder =
    TermBuilder.pi("_", arg)(_ => this)
  final def eval(): Term = this.build().nf()

object TermBuilder:
  private final def level(level: Int) =
    TermBuilder((varLvl: Int, _) => Term.TVar(varLvl - 1 - level))

  final def U: TermBuilder = TermBuilder((_, _) => Term.TU)

  final def hole: TermBuilder =
    TermBuilder((_, metaGen: MetaGenerator) => Term.TMeta(metaGen()))

  final def pi(name: String, ty: TermBuilder)(
      body: TermBuilder => TermBuilder
  ): TermBuilder =
    TermBuilder((bindLvl: Int, metaGen: MetaGenerator) =>
      Term.TPi(
        name,
        ty.builder(bindLvl, metaGen),
        body(level(bindLvl)).builder(bindLvl + 1, metaGen)
      )
    )

  final def let(name: String, ty: TermBuilder, is: TermBuilder)(
      in: TermBuilder => TermBuilder
  ): TermBuilder =
    TermBuilder((bindLvl, metaGen) =>
      Term.TLet(
        name,
        ty.builder(bindLvl, metaGen),
        is.builder(bindLvl, metaGen),
        in(level(bindLvl)).builder(bindLvl + 1, metaGen)
      )
    )

  final def let(name: String, is: TermBuilder)(
      in: TermBuilder => TermBuilder
  ): TermBuilder = let(name, hole, is)(in)

  final def lam(name: String)(body: TermBuilder => TermBuilder): TermBuilder =
    TermBuilder((bindLvl: Int, metaGen: MetaGenerator) =>
      Term.TAbs(
        name,
        body(level(bindLvl)).builder(bindLvl + 1, metaGen)
      )
    )

  final def lam(name1: String, name2: String)(
      body: (TermBuilder, TermBuilder) => TermBuilder
  ): TermBuilder =
    lam(name1)(x => lam(name2)(y => body(x, y)))

  final def lam(name1: String, name2: String, name3: String)(
      body: (TermBuilder, TermBuilder, TermBuilder) => TermBuilder
  ): TermBuilder =
    lam(name1)(x => lam(name2)(y => lam(name3)(z => body(x, y, z))))

  final def lam(name1: String, name2: String, name3: String, name4: String)(
      body: (TermBuilder, TermBuilder, TermBuilder, TermBuilder) => TermBuilder
  ): TermBuilder =
    lam(name1)(p =>
      lam(name2)(q => lam(name3)(r => lam(name4)(s => body(p, q, r, s))))
    )

object EvalExamples:
  import TermBuilder._

  final def nat(x: Int): TermBuilder =
    TermBuilder.lam("s")(s =>
      TermBuilder.lam("z")(z => 1.to(x).foldLeft(z)((t, _) => s(t)))
    )

  final def zero: TermBuilder = lam("s", "z")((_, z) => z)
  final def inc: TermBuilder = lam("a", "s", "z")((a, s, z) => s(a(s, z)))
  final def add: TermBuilder =
    lam("a", "b", "s", "z")((a, b, s, z) => a(s, b(s, z)))
  final def mul: TermBuilder =
    lam("a", "b", "s", "z")((a, b, s, z) => a(b(s), z))
  final def pair: TermBuilder = lam("a", "b", "s")((a, b, s) => s(a, b))
  final def tt: TermBuilder = lam("a", "_")((a, _) => a)
  final def ff: TermBuilder = lam("_", "b")((_, b) => b)
  final def fst: TermBuilder = lam("p")(_(tt))
  final def snd: TermBuilder = lam("p")(_(ff))
  final def pred: TermBuilder =
    lam("n")(n =>
      fst(n(lam("p")(p => pair(snd(p), inc(snd(p)))), pair(zero, zero)))
    )
  final def sub: TermBuilder =
    lam("a", "b")((a, b) => b(pred, a))

  /* Church-encoded arithmetic expressions in lambda calculus */
  final def mkOp(
      op: ((TermBuilder, TermBuilder, TermBuilder)) => TermBuilder
  ): TermBuilder =
    lam("e1", "e2")((e1, e2) =>
      lam("fAdd", "fSub", "fMul", "fN")((fAdd, fSub, fMul, fN) =>
        op((fAdd, fSub, fMul))(
          e1(fAdd, fSub, fMul, fN),
          e2(fAdd, fSub, fMul, fN)
        )
      )
    )

  final def mkAdd = mkOp(_._1)
  final def mkSub = mkOp(_._2)
  final def mkMul = mkOp(_._3)

  final def liftN =
    lam("n")(n => lam("_", "_", "_", "fN")((_, _, _, fN) => fN(n)))

class EvalTestSuite extends AnyFunSuite {
  import TermBuilder._
  import EvalExamples._

  test("10 - 5 = 5") {
    assert(sub(nat(10), nat(5)).eval() == nat(5).build())
  }

  test("(5 + 5) * (5 + 5) * (5 + 5) = 1000  (02-typecheck-closures-debruijn)") {
    assert(let("add", add) { add =>
      let("mul", mul) { mul =>
        let("five", nat(5)) { five =>
          let("ten", add(five, five)) { ten =>
            let("hundred", mul(ten, ten)) { hundred =>
              let("thousand", mul(hundred, ten))(thousand => thousand)
            }
          }
        }
      }
    }.eval() == nat(1000).build())
  }

  test("staged (3 * 2) + (3 - 1) = 14") {
    assert(
      lam("e")(e => e(add, sub, mul, lam("x") { x => x }))(
        mkAdd(
          mkMul(liftN(nat(4)), liftN(nat(3))),
          mkSub(liftN(nat(3)), liftN(nat(1)))
        )
      ).eval() == nat(14).build()
    )
  }

}

final class TypecheckingFailedException() extends Exception

def unify(v1: Val, v2: Val, envSize: Int): Unit =

  /* Simple untyped pattern unification */
  def solve(meta: Meta, sp: Spine, rhs: Val, envSize: Int): Unit =
    case class InvertedSpine(
        val srcEnvSize: Int,
        val targetEnvSize: Int = 0,
        val map: Map[Int, Int] = Map.empty,
        val nonlinear: Set[Int] = Set.empty
    ):
      def extend(srcLvl: Int): InvertedSpine =
        if (nonlinear.contains(srcLvl) || map.contains(srcLvl))
          InvertedSpine(
            srcEnvSize,
            targetEnvSize + 1,
            map - srcLvl,
            nonlinear + srcLvl
          )
        else
          InvertedSpine(
            srcEnvSize,
            targetEnvSize + 1,
            map + (srcLvl -> targetEnvSize),
            nonlinear
          )

      def lift(): InvertedSpine = InvertedSpine(
        srcEnvSize + 1,
        targetEnvSize + 1,
        map + (srcEnvSize -> targetEnvSize),
        nonlinear
      )

      def getVarAtlvl(srcLvl: Int): Term.TVar = Term.TVar(
        targetEnvSize - 1 - map.getOrElse(
          srcLvl,
          throw TypecheckingFailedException()
        )
      )

    /* Returns a mapping with de-brujin level equivalents in empty context. */
    /* Maps to None if there were multiple occurances of the variable in the spine. */
    @tailrec
    def invertSpine(
        sp: Spine,
        acc: InvertedSpine
    ): InvertedSpine =
      sp match
        case (Elim.EApp(v) +: sp) =>
          v.force() match
            case Val.VStuck(Head.HNeutral(n), IndexedSeq()) =>
              invertSpine(sp, acc.extend(n))
            case _ => throw TypecheckingFailedException()
        case IndexedSeq() => acc
        case _            => throw TypecheckingFailedException()

    def rename(
        v: Val,
        meta: Meta,
        invertedSpine: InvertedSpine
    ): Term = v.force() match

      case Val.VAbs(closure) =>
        Term.TAbs(
          closure.name,
          rename(
            closure(Val.bound(envSize)),
            meta,
            invertedSpine.lift()
          )
        )

      case Val.VPi(ty, closure) =>
        Term.TPi(
          closure.name,
          rename(ty, meta, invertedSpine),
          rename(
            closure(Val.bound(envSize)),
            meta,
            invertedSpine.lift()
          )
        )

      case Val.VU => Term.TU

      case Val.VStuck(hd, sp) =>
        sp.foldLeft(
          hd match
            case Head.HNeutral(lvl) =>
              invertedSpine.getVarAtlvl(lvl)
            case Head.HMeta(innerMeta) =>
              if innerMeta.id == meta.id then
                throw TypecheckingFailedException()
              else Term.TMeta(meta)
        )((head, elim) =>
          elim match
            case Elim.EApp(arg) =>
              Term.TApp(head, rename(arg, meta, invertedSpine))
        )

    meta.solve(
      1.to(sp.length)
        .reverseIterator
        .foldLeft(
          rename(
            rhs,
            meta,
            invertSpine(sp, InvertedSpine(srcEnvSize = envSize))
          )
        )((r, n) => Term.TAbs(s"t$n", r))
        .eval() // Doesn't actually reduce anything
    )

  @tailrec
  def unifySpines(sp1: Spine, sp2: Spine, envSize: Int): Unit =
    (sp1, sp2) match
      case (Elim.EApp(v1) +: sp1, Elim.EApp(v2) +: sp2) =>
        unify(v1, v2, envSize); unifySpines(sp1, sp2, envSize)
      case (IndexedSeq(), IndexedSeq()) => ()
      case _                            => throw TypecheckingFailedException()

  def unify(v1: Val, v2: Val, envSize: Int): Unit =
    (v1.force(), v2.force()) match
      case (Val.VAbs(c1), Val.VAbs(c2)) =>
        unify(c1(Val.bound(envSize)), c2(Val.bound(envSize)), envSize + 1)
      /* Dealing with eta-equality */
      case (Val.VAbs(c1), t2) =>
        unify(c1(Val.bound(envSize)), t2(Val.bound(envSize)), envSize + 1)
      case (t1, Val.VAbs(c2)) =>
        unify(t1(Val.bound(envSize)), c2(Val.bound(envSize)), envSize + 1)
      case (Val.VU, Val.VU) => ()
      case (Val.VPi(argTy1, bodyTyClosure1), Val.VPi(argTy2, bodyTyClosure2)) =>
        unify(argTy1, argTy2, envSize)
        unify(
          bodyTyClosure1(Val.bound(envSize)),
          bodyTyClosure2(Val.bound(envSize)),
          envSize + 1
        )
      case (Val.VStuck(hd1, sp1), Val.VStuck(hd2, sp2)) if hd1 == hd2 =>
        unifySpines(sp1, sp2, envSize)
      case (Val.VStuck(Head.HMeta(m1), sp1), rhs) =>
        solve(m1, sp1, rhs, envSize)
      case (lhs, Val.VStuck(Head.HMeta(m2), sp2)) =>
        solve(m2, sp2, lhs, envSize)
      case _ =>
        throw TypecheckingFailedException()

  unify(v1, v2, envSize)

enum Raw:
  case RVar(name: String)
  case RApp(fun: Raw, arg: Raw)
  case RAbs(name: String, body: Raw)
  case RPi(name: String, ty: Raw, body: Raw)
  case RLet(name: String, ty: Raw, is: Raw, in: Raw)
  case RU
  case RHole

  def apply(args: Raw*): Raw =
    args.foldLeft(this)(RApp(_, _))

  def ->:(lhs: Raw): Raw =
    RPi("_", lhs, this)

object Raw:
  def lam(name: String)(f: Raw => Raw): Raw =
    RAbs(name, f(RVar(name)))

  def lam(name1: String, name2: String)(f: (Raw, Raw) => Raw): Raw =
    RAbs(name1, RAbs(name2, f(RVar(name1), RVar(name2))))

  def lam(name1: String, name2: String, name3: String)(
      f: (Raw, Raw, Raw) => Raw
  ): Raw =
    RAbs(
      name1,
      RAbs(name2, RAbs(name3, f(RVar(name1), RVar(name2), RVar(name3))))
    )

  def lam(name1: String, name2: String, name3: String, name4: String)(
      f: (Raw, Raw, Raw, Raw) => Raw
  ): Raw =
    RAbs(
      name1,
      RAbs(
        name2,
        RAbs(
          name3,
          RAbs(name4, f(RVar(name1), RVar(name2), RVar(name3), RVar(name4)))
        )
      )
    )

  def pi(name: String, ty: Raw)(f: Raw => Raw): Raw =
    RPi(name, ty, f(RVar(name)))

  def pi(name1: String, name2: String, ty: Raw)(f: (Raw, Raw) => Raw): Raw =
    RPi(name1, ty, RPi(name2, ty, f(RVar(name1), RVar(name2))))

  def lets(defs: (String, Raw, Raw)*)(t: Raw): Raw =
    defs.foldRight(t)((let, in) => RLet(let._1, let._2, let._3, in))

  def let(name: String, ty: Raw, is: Raw)(f: Raw => Raw): Raw =
    RLet(name, ty, is, f(RVar(name)))

  def hole = RHole
  def U = RU

trait TypecheckTrace:
  def checkBegin(term: Raw, ty: Val, envSize: Int): Unit = ()
  def inferBegin(term: Raw): Unit = ()
  def unifyBegin(val1: Val, val2: Val, envSize: Int): Unit = ()
  def checkEnd(res: Term): Unit = ()
  def inferEnd(res: Term, ty: Val, envSize: Int): Unit = ()
  def unifyEnd(): Unit = ()

  final def wrapCheck(term: Raw, ty: Val, envSize: Int)(ret: => (Term)): Term =
    checkBegin(term, ty, envSize)
    val res = ret
    checkEnd(res)
    res

  final def wrapInfer(term: Raw, envSize: Int)(
      ret: => (Term, Val)
  ): (Term, Val) =
    inferBegin(term)
    val (res, ty) = ret
    inferEnd(res, ty, envSize)
    (res, ty)

  final def doUnify(val1: Val, val2: Val, envSize: Int): Unit =
    unifyBegin(val1, val2, envSize)
    unify(val1, val2, envSize)
    unifyEnd()

class NoOpTypecheckTrace() extends TypecheckTrace

class VerboseTypecheckTrace(
    stream: java.io.PrintStream = System.err,
    private var indentLevel: Int = 0
) extends TypecheckTrace:
  def printPrefix(): Unit =
    stream.print(" " * indentLevel)

  override def checkBegin(term: Raw, ty: Val, envSize: Int): Unit =
    printPrefix()
    stream.println(s"check: $term |- ${ty.quote(envSize)}? {")
    indentLevel += 1

  override def inferBegin(term: Raw): Unit =
    printPrefix()
    stream.println(s"infer: $term? {")
    indentLevel += 1

  override def unifyBegin(val1: Val, val2: Val, envSize: Int): Unit =
    printPrefix()
    stream.print(s"unify: ${val1.quote(envSize)} == ${val2.quote(envSize)}? ")

  override def checkEnd(res: Term): Unit =
    indentLevel -= 1
    printPrefix()
    stream.println(s"} yes, elaborated to $res")

  override def inferEnd(res: Term, ty: Val, envSize: Int): Unit =
    indentLevel -= 1
    printPrefix()
    stream.println(s"} elaborated to $res, type ${ty.quote(envSize)}")

  override def unifyEnd(): Unit =
    stream.println(" yes!")

class Context(
    val env: Env = Vector.empty,
    val bds: Vector[BD] = Vector.empty,
    val tys: Vector[Val] = Vector.empty,
    val names: Vector[String] = Vector.empty,
    val nameToLvl: Map[String, Int] = Map.empty,
    val trace: TypecheckTrace = NoOpTypecheckTrace(),
    val metaGen: MetaGenerator = MetaGenerator()
):
  def metas(): Vector[Meta] = metaGen.metas()
  def extend(name: String, ty: Val, bd: BD, v: Val): Context =
    Context(
      env :+ v,
      bds :+ bd,
      tys :+ ty,
      names :+ name,
      nameToLvl + (name -> env.length),
      trace,
      metaGen
    )

  def bindAtEnd(name: String, ty: Val): Context =
    extend(name, ty, BD.Bound, newAtEnd)
  def defineAtEnd(name: String, ty: Val, v: Val): Context =
    extend(name, ty, BD.Defined, v)

  def envSize = env.length
  def newAtEnd = Val.bound(envSize)
  def getLvl(name: String) =
    nameToLvl.get(name).getOrElse(throw TypecheckingFailedException())

  def inferVar(name: String): (Term, Val) =
    val lvl = getLvl(name)
    (Term.TVar(envSize - 1 - lvl), tys(lvl))

  def insertedMeta(): Term.TInsertedMeta =
    Term.TInsertedMeta(metaGen(), bds)

  def infer(term: Raw): (Term, Val) = trace.wrapInfer(term, envSize)(term match
    case Raw.RVar(name) => inferVar(name)
    case Raw.RApp(fun, arg) =>
      val (elaboratedFun, funTy) = infer(fun)
      // LHS needs to be a Pi type. We are interested in its components -
      // type of the argument and closure for the return type
      val (argTy, bodyTyClosure) = funTy.force() match
        case Val.VPi(argTy, bodyTyClosure) =>
          (argTy, bodyTyClosure)
        case Val.VU | Val.VAbs(_) => throw TypecheckingFailedException()
        case Val.VStuck(hd, sp)   =>
          // This might potentially resolve to a Pi type later, so we need
          // to create two metas for two components of the Pi type, hoping
          // that we don't make a mistake
          val argTy = insertedMeta().eval(env)
          (argTy, Closure("x", env, bindAtEnd("x", argTy).insertedMeta()))

      val elaboratedArg = check(arg, argTy)
      (
        Term.TApp(elaboratedFun, elaboratedArg),
        bodyTyClosure(elaboratedArg.eval(env))
      )

    case Raw.RAbs(name, body) =>
      val argTy = insertedMeta().eval(env)
      val (elaboratedBody, bodyTy) =
        bindAtEnd(name, argTy).infer(body)
      (
        Term.TAbs(name, elaboratedBody),
        Val.VPi(argTy, Closure(name, env, bodyTy.quote(envSize + 1)))
      )

    case Raw.RPi(name, argTy, retTy) =>
      val elaboratedArgTy = check(argTy, Val.VU)
      val elaboratedRetTy =
        bindAtEnd(name, elaboratedArgTy.eval(env)).check(retTy, Val.VU)
      (Term.TPi(name, elaboratedArgTy, elaboratedRetTy), Val.VU)

    case Raw.RLet(name, defTy, is, in) =>
      val elaboratedTy = check(defTy, Val.VU)
      val evaluatedTy = elaboratedTy.eval(env)
      val elaboratedIs = check(is, evaluatedTy)
      val evaluatedIs = elaboratedIs.eval(env)
      val (elaboratedIn, inTy) =
        defineAtEnd(name, evaluatedTy, evaluatedIs).infer(in)
      (Term.TLet(name, elaboratedTy, elaboratedIs, elaboratedIn), inTy)

    case Raw.RU => (Term.TU, Val.VU)
    case Raw.RHole =>
      val tMeta = insertedMeta()
      (tMeta, Val.meta(tMeta.meta))
  )

  def check(term: Raw, ty: Val): Term =
    trace.wrapCheck(term, ty, envSize)((term, ty.force()) match
      case (Raw.RAbs(name, body), Val.VPi(argTy, closure)) =>
        val bodyTy = closure(newAtEnd)
        Term.TAbs(
          name,
          bindAtEnd(name, argTy).check(body, bodyTy)
        )

      case (Raw.RLet(name, defTy, is, in), ty) =>
        val elaboratedTy = check(defTy, Val.VU)
        val evaluatedTy = elaboratedTy.eval(env)
        val elaboratedIs = check(is, evaluatedTy)
        val evaluatedIs = elaboratedIs.eval(env)
        val elaboratedIn =
          defineAtEnd(name, evaluatedTy, evaluatedIs).check(in, ty)
        Term.TLet(name, elaboratedTy, elaboratedIs, elaboratedIn)

      case (Raw.RHole, ty) => insertedMeta()
      case _ =>
        val (elaborated, actualTy) = infer(term)
        trace.doUnify(actualTy, ty, envSize)
        elaborated
    )

  def elab(term: Raw): (Term, Term) =
    val (elaboratedTerm, termTy) = infer(term)
    (elaboratedTerm, termTy.quote(0))

object TypecheckExamples:
  import Raw._

  /* Examples from https://github.com/AndrasKovacs/elaboration-zoo/blob/master/02-typecheck-closures-debruijn/Main.hs */

  def church(n: Int) = RAbs(
    "N",
    RAbs(
      "s",
      RAbs("z", 1.to(n).foldLeft(RVar("z"))((arg, _) => RApp(RVar("s"), arg)))
    )
  )

  def ex0 =
    let("id", pi("A", U)(A => A ->: A), lam("A", "x")((A, x) => x)) { id =>
      let("foo", U, U)(foo => let("bar", U, id(id))(bar => id))
    }

  def ex1 =
    let("id", pi("A", U)(A => A ->: A), lam("A", "x")((A, x) => x)) { id =>
      let(
        "const",
        pi("A", "B", U)((A, B) => A ->: (B ->: A)),
        lam("A", "B", "x", "y")((A, B, x, y) => x)
      ) { const =>
        id(pi("A", "B", U)((A, B) => A ->: (B ->: A)), const)
      }
    }

  def ex2 =
    let("Nat", U, pi("N", U)(N => (N ->: N) ->: N ->: N)) { Nat =>
      let("five", Nat, church(5)) { five =>
        let(
          "add",
          Nat ->: Nat ->: Nat,
          lam("a", "b")((a, b) =>
            lam("N", "s", "z")((N, s, z) => a(N, s, b(N, s, z)))
          )
        ) { add =>
          let(
            "mul",
            Nat ->: Nat ->: Nat,
            lam("a", "b")((a, b) =>
              lam("N", "s", "z")((N, s, z) => a(N, b(N, s), z))
            )
          ) { mul =>
            let("ten", Nat, add(five, five)) { ten =>
              let("hundred", Nat, mul(ten, ten)) { hundred =>
                let("thousand", Nat, mul(ten, hundred)) { thousand => thousand }
              }
            }
          }
        }
      }
    }

  /* https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/example.txt */
  def ex03Holes = lets(
    ("id", pi("A", hole)(A => A ->: A), lam("A", "x")((A, x) => x)),
    (
      "List",
      U ->: U,
      lam("A")(A => pi("L", hole)(L => (A ->: L ->: L) ->: L ->: L))
    ),
    (
      "nil",
      pi("A", hole)(A => RVar("List")(A)),
      lam("A", "L", "cons", "nil")((A, L, cons, nil) => nil)
    ),
    (
      "cons",
      pi("A", hole)(A => A ->: RVar("List")(A) ->: RVar("List")(A)),
      lam("A", "x", "xs")((A, x, xs) =>
        lam("L", "cons", "nil")((L, cons, nil) => cons(x, xs(hole, cons, nil)))
      )
    ),
    (
      "Bool",
      U,
      pi("B", hole)(B => B ->: B ->: B)
    ),
    (
      "true",
      RVar("Bool"),
      lam("B", "t", "f")((B, t, f) => t)
    ),
    (
      "false",
      RVar("Bool"),
      lam("B", "t", "f")((B, t, f) => f)
    ),
    (
      "not",
      RVar("Bool") ->: RVar("Bool"),
      lam("b", "B", "t", "f")((b, B, t, f) => b(B, f, t))
    ),
    (
      "list1",
      RVar("List")(RVar("Bool")),
      RVar("cons")(
        hole,
        RVar("id")(hole, RVar("true")),
        RVar("nil")(hole)
      )
    ),
    (
      "Eq",
      pi("A", hole)(A => A ->: A ->: U),
      lam("A", "x", "y")((A, x, y) => pi("P", A ->: U)(P => P(x) ->: P(y)))
    ),
    (
      "refl",
      pi("A", hole)(A => pi("x", A)(x => RVar("Eq")(A, x, x))),
      lam("A", "x", "P", "px")((A, x, P, px) => px)
    ),
    (
      "list1",
      RVar("List")(RVar("Bool")),
      RVar("cons")(
        hole,
        RVar("true"),
        RVar("cons")(hole, RVar("false"), RVar("nil")(hole))
      )
    ),
    ("Nat", U, pi("N", U)(N => (N ->: N) ->: N ->: N)),
    ("five", RVar("Nat"), church(5)),
    (
      "add",
      RVar("Nat") ->: RVar("Nat") ->: RVar("Nat"),
      lam("a", "b")((a, b) =>
        lam("N", "s", "z")((N, s, z) => a(N, s, b(N, s, z)))
      )
    ),
    (
      "mul",
      RVar("Nat") ->: RVar("Nat") ->: RVar("Nat"),
      lam("a", "b")((a, b) => lam("N", "s", "z")((N, s, z) => a(N, b(N, s), z)))
    ),
    ("ten", RVar("Nat"), RVar("add")(RVar("five"), RVar("five"))),
    ("hundred", RVar("Nat"), RVar("mul")(RVar("ten"), RVar("ten"))),
    ("thousand", RVar("Nat"), RVar("mul")(RVar("ten"), RVar("hundred"))),
    (
      "eqTest",
      RVar("Eq")(hole, RVar("hundred"), RVar("hundred")),
      RVar("refl")(hole, hole)
    )
  )(U)

class TypecheckTestSuite extends AnyFunSuite {
  import TypecheckExamples._

  test("ex0 from 02-typecheck-closures-debruijn does not typecheck") {
    assertThrows[TypecheckingFailedException](Context().elab(ex0))
  }

  test("ex1 from 02-typecheck-closures-debruijn (id and const) typechecks") {
    val (_, ty) = Context().elab(ex1)

    import TermBuilder._
    assert(ty == pi("A", U)(A => pi("B", U)(B => A ->: B ->: A)).build())
  }

  test("ex2 from 02-typecheck-closures-debruijn (thousand) typechecks") {
    val (_, ty) = Context().elab(ex2)

    import TermBuilder._
    assert(ty == pi("N", U)(N => (N ->: N) ->: N ->: N).build())
  }

  test("Example from 03-holes typechecks") {
    Context().elab(ex03Holes)
  }

}

object Hello:
  final def main(args: Array[String]) =
    println("Nothing to see here, use scala-cli test instead")
