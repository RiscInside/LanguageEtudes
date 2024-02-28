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

(* TODO: this is currently slower than it should be. Investigate *)
module Zinc = struct
  type ins =
    | Grab
    | Return
    | Access of int
    | Closure of ins list
    | PushRetAddr of ins list
    | TailApply

  let compile_var (n : int) : ins = Access n

  let rec compile (t : tm) (cont : ins list) : ins list =
    match t with
    | TVar i -> compile_var i :: cont
    | TApp (f, a) -> PushRetAddr cont :: compile_app f a
    | TLam b -> Closure (Grab :: compile_tail b) :: cont

  and compile_app (f : tm) (a : tm) : ins list =
    match f with
    | TApp (f', a') -> compile a (compile_app f' a')
    | f -> compile a (compile f [ TailApply ])

  and compile_tail : tm -> ins list = function
    | TLam b -> Grab :: compile_tail b
    | TApp (f, a) -> compile_app f a
    | TVar i -> [ compile_var i; Return ]

  type value =
    | VNeu of int
    | VApp of value * value
    | VLam of ins list * value list

  type stack =
    | SNil
    | SValue of (value * stack)
    | SMarker of ins list * value list * stack

  exception InterpreterError of ins list * stack * value list
  exception CantQuoteClosure of ins list * value list

  let rec interpret (insns : ins list) (stack : stack) (env : value list) :
      value =
    match (insns, stack, env) with
    | [], SValue (res, stack), _ -> res
    (* *)
    | Grab :: insns, SMarker (insns', env', stack), env ->
        interpret insns' (SValue (VLam (Grab :: insns, env), stack)) env'
    | Grab :: insns, SValue (value, stack), env ->
        interpret insns stack (value :: env)
    | Grab :: _, SNil, env -> VLam (insns, env)
    (* *)
    | Return :: _, SValue (VLam (insns, env), stack), _ ->
        interpret insns stack env
    | Return :: _, SValue (value, SMarker (insns, env, stack)), _ ->
        interpret insns (SValue (value, stack)) env
    | Return :: _, SValue (value, SNil), _ -> value
    (* *)
    | Access i :: insns, stack, env ->
        interpret insns (SValue (nth env i, stack)) env
    (* *)
    | Closure insns' :: insns, stack, env ->
        interpret insns (SValue (VLam (insns', env), stack)) env
    (* *)
    | PushRetAddr insns' :: insns, stack, env ->
        interpret insns (SMarker (insns', env, stack)) env
    (* *)
    | TailApply :: _, SValue (VLam (insns, env), stack), _ ->
        interpret insns stack env
    (* Building applications until stack becomes empty or we see a marker *)
    | TailApply :: _, SValue (v, SValue (i, stack)), env ->
        interpret insns (SValue (VApp (v, i), stack)) env
    | TailApply :: _, SValue (v, SNil), _ -> v
    | TailApply :: _, SValue (v, SMarker (insns, env, stack)), _ ->
        interpret insns (SValue (v, stack)) env
    (* *)
    | _, _, _ -> raise (InterpreterError (insns, stack, env))

  let rec quote (bindings : int) : value -> tm = function
    | VNeu lvl -> TVar (bindings - lvl - 1)
    | VApp (v1, v2) -> TApp (quote bindings v1, quote bindings v2)
    | VLam (Grab :: insns, env) ->
        TLam
          (quote (bindings + 1) (interpret insns SNil (VNeu bindings :: env)))
    | VLam (insns, env) -> raise (CantQuoteClosure (insns, env))

  let rec nf (t : tm) : tm = quote 0 (interpret (compile t []) SNil [])
end

(* Uhh *)
external unsafe_set_uint16_ne : bytes -> int -> int -> unit
  = "%caml_bytes_set16u"

external unsafe_get_uint16_ne : bytes -> int -> int = "%caml_bytes_get16u"

(* Converting terms to byte sequences *)
module TermMarshal = struct
  let byte_var_boundary : int = 0xfc
  let short_var_marker : char = '\xfd'
  let app_byte : char = '\xfe'
  let lam_byte : char = '\xff'

  type writer = { mutable bytes : bytes; mutable offset : int }

  let new_writer () : writer = { bytes = Bytes.create 128; offset = 0 }

  let grow (w : writer) : unit =
    w.bytes <- Bytes.extend w.bytes 0 (Bytes.length w.bytes)

  let rec write (w : writer) (size : int) (f : bytes -> int -> unit) : unit =
    if Bytes.length w.bytes < w.offset + size then grow w else ();
    f w.bytes w.offset;
    w.offset <- w.offset + size

  let write_char (w : writer) (c : char) : unit =
    write w 1 (fun b i -> Bytes.unsafe_set b i c)

  let write_uint16 (w : writer) (v : int) : unit =
    write w 2 (fun b i -> unsafe_set_uint16_ne b i v)

  let make_uint16_hole (w : writer) : int =
    let offset = w.offset in
    write_uint16 w 0;
    offset

  let fill_uint16_hole (w : writer) (hole : int) (v : int) : unit =
    Bytes.set_uint16_ne w.bytes hole v

  exception MarshallingError of string

  let rec marshal (w : writer) (t : tm) : int =
    let rec go (w : writer) : tm -> unit = function
      | TApp (t1, t2) ->
          let start_offset = w.offset in
          write_char w app_byte;
          let offset_hole = make_uint16_hole w in
          go w t1;
          fill_uint16_hole w offset_hole (w.offset - start_offset);
          go w t2
      | TLam b ->
          write_char w lam_byte;
          go w b
      | TVar v ->
          if v <= byte_var_boundary then write_char w (char_of_int v)
          else if v < 65536 then (
            write_char w short_var_marker;
            write_uint16 w v)
          else raise (MarshallingError "variable too big")
    in

    let offset = w.offset in
    go w t;
    offset
end

module MarshalledEval = struct
  (* int in VLam represents byte offset into the buffer where marshalled term starts *)
  type value = VLam of int * value list | VNeu of int | VApp of value * value

  let rec eval (b : bytes) (pc : int) (env : value list) : value =
    match Bytes.unsafe_get b pc with
    | '\xfd' ->
        (* Far variable access *)
        nth env (unsafe_get_uint16_ne b (pc + 1))
    | '\xfe' ->
        (* Function application *)
        let a_offset = unsafe_get_uint16_ne b (pc + 1) in
        let f = eval b (pc + 3) env in
        let a = eval b (pc + a_offset) env in
        apply b f a
    | '\xff' ->
        (* Lamdba abstraction *)
        VLam (pc + 1, env)
    | c ->
        (* Close variable access *)
        nth env (int_of_char c)

  and apply (b : bytes) (f : value) (a : value) : value =
    match f with VLam (off, env) -> eval b off (a :: env) | _ -> VApp (f, a)

  let rec quote (b : bytes) (bindings : int) : value -> tm = function
    | VNeu lvl -> TVar (bindings - lvl - 1)
    | VApp (v1, v2) -> TApp (quote b bindings v1, quote b bindings v2)
    | VLam (off, env) ->
        TLam (quote b (bindings + 1) (eval b off (VNeu bindings :: env)))

  let rec nf (t : tm) : tm =
    let w = TermMarshal.new_writer () in
    let offset = TermMarshal.marshal w t in
    quote w.bytes 0 (eval w.bytes offset [])
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
  benchmark "plain NbE over marshalled terms (1000 - 1000)"
    (TLam (TLam (TVar 0))) (fun _ -> MarshalledEval.nf (testTerm 1000));
  benchmark "cps NbE (1000 - 1000)" (TLam (TLam (TVar 0))) (fun _ ->
      CPSEval.nf (testTerm 1000));
  benchmark "1000 - 1000 on Zinc machine" (TLam (TLam (TVar 0))) (fun _ ->
      Zinc.nf (testTerm 1000));
  benchmark "plain NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      PlainEval.nf (testTerm 3000));
  benchmark "plain NbE over marshalled terms (3000 - 3000)"
    (TLam (TLam (TVar 0))) (fun _ -> MarshalledEval.nf (testTerm 3000));
  benchmark "cps NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      CPSEval.nf (testTerm 3000));
  benchmark "3000 - 3000 on Zinc machine" (TLam (TLam (TVar 0))) (fun _ ->
      Zinc.nf (testTerm 3000));
  benchmark "plain NbE (7000 - 7000)" (TLam (TLam (TVar 0))) ~runs:3 (fun _ ->
      PlainEval.nf (testTerm 7000));
  benchmark "plain NbE over marshalled terms (7000 - 7000)"
    (TLam (TLam (TVar 0))) ~runs:3 (fun _ -> MarshalledEval.nf (testTerm 7000));
  benchmark "7000 - 7000 on Zinc machine" (TLam (TLam (TVar 0))) ~runs:3
    (fun _ -> Zinc.nf (testTerm 7000))
