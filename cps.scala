// Plain and CPS-transformed NbE evaluators for plain lambda calculus.
// CPS-transformed evaluator appears to be 5 times slower on the benchmark,
// but it never runs out of stack space. How can its performance be improved?

package cps

import scala.annotation.tailrec

type Env = Vector[Val]

enum Term:
  case Var(idx: Int)
  case App(fun: Term, arg: Term)
  case Lam(body: Term)

  final def eval(env: Env): Val =
    def apply(lhs: Val, rhs: Val): Val = lhs match
      case Val.Lam(env, body) => body.eval(rhs +: env)
      case _                  => Val.App(lhs, rhs)

    this match
      case Var(idx)      => env(idx)
      case App(fun, arg) => apply(fun.eval(env), arg.eval(env))
      case Lam(body)     => Val.Lam(env, body)

  final def evalCPS(env: Env): Val =
    enum Cont:
      case Id
      case EvalArg(arg: Term, env: Env, cont: Cont)
      case Apply(funV: Val, cont: Cont)

    enum State:
      case ApplyCont(v: Val, cont: Cont)
      case Eval(term: Term, env: Env, cont: Cont)

      @tailrec final def apply(): Val = this match
        case ApplyCont(v, cont) =>
          cont match
            case Cont.Id => v
            case Cont.EvalArg(arg, env, cont) =>
              Eval(arg, env, Cont.Apply(v, cont))()
            case Cont.Apply(funV, cont) =>
              funV match
                case Val.Lam(env, body) => Eval(body, v +: env, cont)()
                case _                  => ApplyCont(Val.App(funV, v), cont)()
        case Eval(term, env, cont) =>
          term match
            case Var(idx)      => ApplyCont(env(idx), cont)()
            case App(fun, arg) => Eval(fun, env, Cont.EvalArg(arg, env, cont))()
            case Lam(body)     => ApplyCont(Val.Lam(env, body), cont)()

    State.Eval(this, env, Cont.Id)()

  def nf(): Term = eval(Vector.empty).quote()
  def nfCPS(): Term = evalCPS(Vector.empty).quoteCPS()

enum Val:
  case Neutral(level: Int)
  case App(lhs: Val, rhs: Val)
  case Lam(env: Env, body: Term)

  final def quote(envSize: Int = 0): Term = this match
    case Neutral(level) => Term.Var(envSize - level - 1)
    case App(lhs, rhs)  => Term.App(lhs.quote(envSize), rhs.quote(envSize))
    case Lam(env, body) =>
      Term.Lam(body.eval(Val.Neutral(envSize) +: env).quote(envSize + 1))

  final def quoteCPS(envSize: Int = 0): Term =
    enum Cont:
      case Id
      case PutUnderBinder(cont: Cont)
      case QuoteRHS(envSize: Int, rhs: Val, cont: Cont)
      case BuildQuotedApp(lhs: Term, cont: Cont)

    enum State:
      case ApplyCont(term: Term, cont: Cont)
      case Quote(v: Val, envSize: Int, cont: Cont)

      @tailrec final def apply(): Term = this match
        case ApplyCont(term, cont) =>
          cont match
            case Cont.Id                   => term
            case Cont.PutUnderBinder(cont) => ApplyCont(Term.Lam(term), cont)()
            case Cont.QuoteRHS(envSize, rhs, cont) =>
              Quote(rhs, envSize, Cont.BuildQuotedApp(term, cont))()
            case Cont.BuildQuotedApp(lhs, cont) =>
              ApplyCont(Term.App(lhs, term), cont)()
        case Quote(v, envSize, cont) =>
          v match
            case Neutral(level) =>
              ApplyCont(Term.Var(envSize - level - 1), cont)()
            case App(lhs, rhs) =>
              Quote(lhs, envSize, Cont.QuoteRHS(envSize, rhs, cont))()
            case Lam(env, body) =>
              Quote(
                body.evalCPS(Val.Neutral(envSize) +: env),
                envSize + 1,
                Cont.PutUnderBinder(cont)
              )()

    State.Quote(this, envSize, Cont.Id)()

class TermBuilder(private val f: (Int) => Term):
  final def build(): Term = f(0)
  final def apply(tbs: TermBuilder*): TermBuilder =
    tbs.foldLeft(this)((fun, arg) =>
      TermBuilder(levels => Term.App(fun.f(levels), arg.f(levels)))
    )

object TermBuilder:
  final def level(level: Int) =
    TermBuilder(varLvl => Term.Var(varLvl - 1 - level))

  final def lam(f: TermBuilder => TermBuilder): TermBuilder =
    TermBuilder(bindLvl => Term.Lam(f(level(bindLvl)).f(bindLvl + 1)))

  final def lam(f: (TermBuilder, TermBuilder) => TermBuilder): TermBuilder =
    lam(arg1 => lam(arg2 => f(arg1, arg2)))

  final def lam(
      f: (TermBuilder, TermBuilder, TermBuilder) => TermBuilder
  ): TermBuilder =
    lam(arg1 => lam(arg2 => lam(arg3 => f(arg1, arg2, arg3))))

  final def lam(
      f: (TermBuilder, TermBuilder, TermBuilder, TermBuilder) => TermBuilder
  ): TermBuilder =
    lam(arg1 =>
      lam(arg2 => lam(arg3 => lam(arg4 => f(arg1, arg2, arg3, arg4))))
    )

import TermBuilder._

def church(n: Int) = lam((s, z) => 1.to(n).foldLeft(z)((arg, _) => s(arg)))
def inc = lam((n, s, z) => s(n(s, z)))
val add = lam((a, b, s, z) => a(s, b(s, z)))
val mul = lam((a, b, s, z) => a(b(s), z))
val pair = lam((a, b, f) => f(a, b))
val fst = lam(p => p(lam((a, _) => a)))
val snd = lam(p => p(lam((_, b) => b)))
val pred =
  lam(n =>
    fst(n(lam(p => pair(snd(p), inc(snd(p)))), pair(church(0), church(0))))
  )
val sub =
  lam((n, m) => m(pred, n))
val testExpr = sub(church(1000), church(1000)).build()

def benchmark(name: String)(run: => Unit) =
  val startTime = System.nanoTime()
  val _ = run
  val endTime = System.nanoTime()
  println(
    s"'${name}' took ${(endTime - startTime).doubleValue() / 1000000000.0} seconds"
  )

object Holes:
  final def main(args: Array[String]) =
    benchmark("quote (1000 - 1000) with normal NbE interpreter")(testExpr.nf())
    benchmark("quote (1000 - 1000) with CPS-transformed interpreter")(
      testExpr.nfCPS()
    )
