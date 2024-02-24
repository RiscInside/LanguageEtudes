type tm = TLam of tm | TApp of tm * tm | TVar of int
type value = VLam of tm * value list | VNeu of int | VApp of value * value

let rec pp_tm (fmt : Format.formatter) (t : tm) : unit =
  match t with
  | TLam t -> Format.fprintf fmt "@[λ.@,%a@]" pp_tm t
  | TApp (t1, t2) -> Format.fprintf fmt "@[(%a)@ (%a)@]" pp_tm t1 pp_tm t2
  | TVar v -> Format.fprintf fmt "%i" v

open List

module PlainEval = struct
  let rec eval (t : tm) (env : value list) : value =
    match t with
    | TVar idx -> nth env idx
    | TApp (lhs, rhs) -> apply (eval lhs env) (eval rhs env)
    | TLam t -> VLam (t, env)

  and apply (f : value) (a : value) : value =
    match f with VLam (fb, fenv) -> eval fb (a :: fenv) | v -> VApp (v, a)

  let rec quote (bindings : int) (v : value) : tm =
    match v with
    | VLam (t, env) ->
        TLam (quote (bindings + 1) (eval t (VNeu bindings :: env)))
    | VApp (t1, t2) -> TApp (quote bindings t1, quote bindings t2)
    | VNeu level -> TVar (bindings - level - 1)

  let nf (t : tm) : tm = quote 0 (eval t [])
end

module CPSEval = struct
  type evalcont =
    | EId
    | EvalArg of tm * value list * evalcont
    | Apply of value * evalcont

  let rec eval (t : tm) (env : value list) (cont : evalcont) : value =
    match t with
    | TVar idx -> (evalcont_apply [@tailcall]) cont (nth env idx)
    | TApp (t1, t2) -> (eval [@tailcall]) t1 env (EvalArg (t2, env, cont))
    | TLam body -> (evalcont_apply [@tailcall]) cont (VLam (body, env))

  and evalcont_apply (cont : evalcont) (v : value) : value =
    match cont with
    | EId -> v
    | EvalArg (t2, env, cont) -> (eval [@tailcall]) t2 env (Apply (v, cont))
    | Apply (VLam (body, env), cont) -> (eval [@tailcall]) body (v :: env) cont
    | Apply (f, cont) -> (evalcont_apply [@tailcall]) cont (VApp (f, v))

  type quotecont =
    | QId
    | PutUnderBinder of quotecont
    | QuoteArg of (int * value * quotecont)
    | BuildApp of tm * quotecont

  let rec quote (bindings : int) (v : value) (cont : quotecont) : tm =
    match v with
    | VLam (t, env) ->
        quote (bindings + 1)
          (eval t (VNeu bindings :: env) EId)
          (PutUnderBinder cont)
    | VNeu lvl -> quotecont_apply cont (TVar (bindings - lvl - 1))
    | VApp (v1, v2) -> quote bindings v1 (QuoteArg (bindings, v2, cont))

  and quotecont_apply (cont : quotecont) (t : tm) : tm =
    match cont with
    | QId -> t
    | PutUnderBinder cont -> quotecont_apply cont (TLam t)
    | QuoteArg (bindings, arg, cont) -> quote bindings arg (BuildApp (t, cont))
    | BuildApp (f, cont) -> quotecont_apply cont (TApp (f, t))

  let nf (t : tm) : tm = quote 0 (eval t [] EId) QId
end

module TB : sig
  type tb

  val lift : tm -> tb
  val ap : tb -> tb -> tb
  val ap2 : tb -> tb -> tb -> tb
  val ap3 : tb -> tb -> tb -> tb -> tb
  val lam : (tb -> tb) -> tb
  val lam2 : (tb -> tb -> tb) -> tb
  val lam3 : (tb -> tb -> tb -> tb) -> tb
  val lam4 : (tb -> tb -> tb -> tb -> tb) -> tb
  val build : tb -> tm
end = struct
  type tb = int -> tm

  let lift t _ = t
  let ap f a levels = TApp (f levels, a levels)
  let ap2 f a b = ap (ap f a) b
  let ap3 f a b c = ap (ap (ap f a) b) c
  let at_lvl l levels = TVar (levels - 1 - l)
  let lam f levels = TLam (f (at_lvl levels) (levels + 1))
  let lam2 f = lam (fun t1 -> lam (fun t2 -> f t1 t2))
  let lam3 f = lam (fun t1 -> lam (fun t2 -> lam (fun t3 -> f t1 t2 t3)))

  let lam4 f =
    lam (fun t1 ->
        lam (fun t2 -> lam (fun t3 -> lam (fun t4 -> f t1 t2 t3 t4))))

  let build f = f 0
end

module TestTerm = struct
  open TB

  let inc = lam3 (fun n s z -> ap s (ap2 n s z))
  let add = lam4 (fun a b s z -> ap2 a s (ap2 b s z))
  let mul = lam4 (fun a b s z -> ap2 a (ap b s) z)
  let pair = lam3 (fun a b f -> ap2 f a b)
  let fst = lam (fun p -> ap p (lam2 (fun a _ -> a)))
  let snd = lam (fun p -> ap p (lam2 (fun _ b -> b)))

  let church n =
    let rec go (acc : tm) (n : int) : tm =
      if n = 0 then acc else go (TApp (TVar 1, acc)) (n - 1)
    in
    lift (TLam (TLam (go (TVar 0) n)))

  let zero = church 0

  let pred =
    lam (fun n ->
        ap fst
          (ap2 n
             (lam (fun p -> ap2 pair (ap snd p) (ap inc (ap snd p))))
             (ap2 pair zero zero)))

  let sub = lam2 (fun n m -> ap2 m pred n)
  let testTerm n = build (ap2 sub (church n) (church n))
end

open TestTerm

let benchmark (name : string) ?(runs : int = 5) (expected : tm) (f : int -> tm)
    =
  let rec go totalTime = function
    | 0 -> totalTime
    | n ->
        Format.printf "Running '%s' (%i runs remaining)\n@?" name n;
        let startT = Sys.time () in
        let actual = f n in
        let endT = Sys.time () in
        if actual <> expected then (
          Format.printf
            "Incorrect result for '%s'@\nexpected: @[%a@]@\nactual: @[%a@]\n@?"
            name pp_tm expected pp_tm actual;
          exit 1)
        else go (totalTime +. (endT -. startT)) (n - 1)
  in

  let res = go 0.0 runs /. float_of_int runs in
  Format.printf "'%s' took %f seconds\n@?" name res

let () =
  benchmark "plain NbE (1000 - 1000)" (TLam (TLam (TVar 0))) (fun _ ->
      PlainEval.nf (testTerm 1000));
  benchmark "cps NbE (1000 - 1000)" (TLam (TLam (TVar 0))) (fun _ ->
      CPSEval.nf (testTerm 1000));
  benchmark "plain NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      PlainEval.nf (testTerm 3000));
  benchmark "cps NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      CPSEval.nf (testTerm 3000));
  benchmark "plain NbE (10000 - 10000)" (TLam (TLam (TVar 0))) ~runs:1 (fun _ ->
      PlainEval.nf (testTerm 10000));
  benchmark "cps NbE (10000 - 10000)" (TLam (TLam (TVar 0))) ~runs:1 (fun _ ->
      CPSEval.nf (testTerm 10000))
