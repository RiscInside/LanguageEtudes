// Plain and CPS-transformed NbE evaluators for plain lambda calculus.
// CPS-transformed evaluator appears to be 5 times slower on the benchmark,
// but it never runs out of stack space. How can its performance be improved?

//> using scala 3

import scala.annotation.tailrec

type Env = Vector[Val]

enum Term:
  case Var(idx: Int)
  case App(fun: Term, arg: Term)
  case Lam(body: Term)

  // Vanilla NbE evaluator
  final def eval(env: Env = Vector.empty): Val =
    def apply(lhs: Val, rhs: Val): Val = lhs match
      case Val.Lam(env, body) => body.eval(rhs +: env)
      case _                  => Val.App(lhs, rhs)

    this match
      case Var(idx)      => env(idx)
      case App(fun, arg) => apply(fun.eval(env), arg.eval(env))
      case Lam(body)     => Val.Lam(env, body)

  // Same evaluator after applying CPS transformation and defunctionalizing
  // continuations (CPS version without defunctionalization wouldn't be tail recursive)
  final def evalCPS(env: Env = Vector.empty): Val =
    enum State:
      case ApplyCont(v: Val, cont: EvalCont)
      case Eval(term: Term, env: Env, cont: EvalCont)

      @tailrec final def apply(): Val = this match
        case ApplyCont(v, cont) =>
          cont match
            case EvalCont.Ret => v
            case EvalCont.EvalArg(arg, env, cont) =>
              Eval(arg, env, EvalCont.Apply(v, cont))()
            case EvalCont.Apply(funV, cont) =>
              funV match
                case Val.Lam(env, body) => Eval(body, v +: env, cont)()
                case _                  => ApplyCont(Val.App(funV, v), cont)()
        case Eval(term, env, cont) =>
          term match
            case Var(idx) => ApplyCont(env(idx), cont)()
            case App(fun, arg) =>
              Eval(fun, env, EvalCont.EvalArg(arg, env, cont))()
            case Lam(body) => ApplyCont(Val.Lam(env, body), cont)()

    State.Eval(this, env, EvalCont.Ret)()

  // We can improve things by getting rid of State ADT and mashing all members
  // together (aka the C way of representing ADTs). The resulting record can
  // then be manually unboxed by splitting one state parameter into all of
  // its members. Since number of parameters rises to 5, I think while
  // loop actually ends up looking nicer here than @tailrec version.
  //
  // Credit to @Labbekak on r/ProgrammingLanguage discord for coming up
  // with the idea, implementing it, and noticing that it makes a very
  // significant difference
  final def evalCPSUgly(env: Env = Vector.empty): Val =
    var isApplyingCont: Boolean = false
    var cont: EvalCont = EvalCont.Ret
    var cenv: Env = env
    var cterm: Term = this
    var cval: Val = null

    inline def switchToEval(
        newTerm: Term,
        newEnv: Env,
        newCont: EvalCont
    ): Unit =
      isApplyingCont = false
      cterm = newTerm
      cenv = newEnv
      cont = newCont

    inline def switchToApplyCont(newVal: Val, newCont: EvalCont): Unit =
      isApplyingCont = true
      cval = newVal
      cont = newCont

    while true do
      if isApplyingCont then
        cont match
          case EvalCont.Ret => return cval
          case EvalCont.Apply(funV, cont) =>
            funV match
              case Val.Lam(env, body) =>
                switchToEval(body, cval +: env, cont)
              case _ => switchToApplyCont(Val.App(funV, cval), cont)
          case EvalCont.EvalArg(arg, env, cont) =>
            switchToEval(arg, env, EvalCont.Apply(cval, cont))
      else
        cterm match
          case Term.Var(idx) => switchToApplyCont(cenv(idx), cont)
          case Term.App(fun, arg) =>
            switchToEval(fun, cenv, EvalCont.EvalArg(arg, cenv, cont))
          case Term.Lam(body) => switchToApplyCont(Val.Lam(cenv, body), cont)
    ???

  // Suspended evaluation. I stole the idea from https://github.com/j-mie6/parsley -
  // parser combinator library that guarantees bounded stack space usage
  final def evalSuspended(env: Env = Vector.empty): Val =
    def evalToSuspended[R](
        term: Term,
        env: Env
    ): SuspendCont[Val, R] =
      term match
        case Var(idx) => SuspendCont.pure(env(idx))
        case App(fun, arg) =>
          SuspendCont.lazyBind(evalToSuspended(fun, env))(fVal =>
            SuspendCont.lazyBind(evalToSuspended(arg, env))(aVal =>
              fVal match
                case Val.Lam(env, body) => evalToSuspended(body, aVal +: env)
                case _                  => SuspendCont.pure(Val.App(fVal, aVal))
            )
          )
        case Lam(body) => SuspendCont.pure(Val.Lam(env, body))

    SuspendCont.run(evalToSuspended(this, env))

  final def nf(): Term = eval().quote(_.eval(_))
  final def nfCPS(): Term = evalCPS().quote(_.evalCPS(_))
  final def nfCPSUgly(): Term =
    evalCPSUgly().quote(_.evalCPSUgly(_))
  final def nfSuspended(): Term = evalSuspended().quote(_.evalSuspended(_))

enum EvalCont:
  case Ret
  case EvalArg(arg: Term, env: Env, cont: EvalCont)
  case Apply(funV: Val, cont: EvalCont)

enum Val:
  case Neutral(level: Int)
  case App(lhs: Val, rhs: Val)
  case Lam(env: Env, body: Term)

  final def quote(eval: (Term, Env) => Val, envSize: Int = 0): Term = this match
    case Neutral(level) => Term.Var(envSize - level - 1)
    case App(lhs, rhs) =>
      Term.App(lhs.quote(eval, envSize), rhs.quote(eval, envSize))
    case Lam(env, body) =>
      Term.Lam(eval(body, Val.Neutral(envSize) +: env).quote(eval, envSize + 1))

enum DoThis[A]:
  case RightNow(res: A)
  case Later(f: () => DoThis[A])

  @tailrec final def run: A = this match
    case RightNow(v) => v
    case Later(f)    => f().run

  // Helper method that calculates how many suspensions we went through
  @tailrec final def runAndCount(acc: Int = 0): (A, Int) = this match
    case RightNow(v) => (v, acc)
    case Later(f)    => f().runAndCount(acc + 1)

type SuspendCont[A, R] = (A => DoThis[R]) => DoThis[R]

object SuspendCont {
  def toDo[A](cont: SuspendCont[A, A]): DoThis[A] = cont(DoThis.RightNow(_))

  def run[A](cont: SuspendCont[A, A]): A = toDo(cont).run

  def pure[A, R](value: => A): SuspendCont[A, R] = f => f(value)

  def lazyMap[A, B, R](cont: => SuspendCont[A, R])(
      f: A => B
  ): SuspendCont[B, R] =
    c => DoThis.Later(() => cont(a => SuspendCont.pure(f(a))(c)))

  def lazyBind[A, B, R](cont: => SuspendCont[A, R])(
      f: A => SuspendCont[B, R]
  ): SuspendCont[B, R] =
    c => DoThis.Later(() => cont(a => f(a)(c)))
}

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

def church(n: Int) = TermBuilder((level) =>
  Term.Lam(
    Term.Lam(
      1.to(n).foldLeft(Term.Var(0))((arg, _) => Term.App(Term.Var(1), arg))
    )
  )
)

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
def testExpr(num: Int) =
  sub(church(num), church(num)).build()

def benchmark[T](name: String, times: Int, warmup: Int = 1)(run: => T) =
  import scala.io.AnsiColor._

  for _ <- 1.to(warmup) do run
  val startTime = System.nanoTime()
  for _ <- 1.to(times) do run
  val endTime = System.nanoTime()
  println(
    s"${BLUE}'${name}' took ${BOLD}${(endTime - startTime)
        .doubleValue() / times / 1000000000.0}${RESET}${BLUE} seconds${RESET}"
  )

import scala.io.AnsiColor._
if args.length < 2 then println("Usage: prog <TERM_SIZE> <RUNS>") else ()

val n = args(0).toInt
val runs = args(1).toInt
val expr: Term = testExpr(n)

try
  benchmark(s"quote ($n - $n) with with normal NbE interpreter", runs)(
    expr.nf()
  )
catch
  case _: StackOverflowError =>
    println(
      s"${RED}${BOLD}normal NbE interpreter has overflowed the stack${RESET}"
    )

benchmark(s"quote ($n - $n) with CPS-transformed interpreter", runs)(
  expr.nfCPS()
)

benchmark(
  s"quote ($n - $n) with a slightly uglier CPS-transformed interpreter",
  runs
)(
  expr.nfCPSUgly()
)

benchmark(
  s"quote ($n - $n) with CPS-interpreter using suspensions",
  runs
)(
  expr.nfSuspended()
)
