(*
  A collection of NbE interpreters. Each one of them exposes a method called nf
  that can be used to get a normal form of an LC term. LC terms are encoded
  with De Brujin indices. NbE semantic domain varies with each interpreter, but
  the default one (based on De Brujin levels) is given below.

  Table of contents:

  - The most basic NbE interpreter. Sufficiently fast, solid choice.

  - NbE interpreter that does a precompilation step to discover nested
    applications/abstractions. On a huge example (10000 - 10000) this
    optimization gives ~10% speedup

  - CPS NbE interpreter. Roughly the same speed as the basic one +
    is guaranteed to use constant amount of stack space. It does allocate
    a lot however, so I noticed that sometimes plain eval would run
    successfully, whereas CPS version would cause OOM killer to nuke OCaml
    process
  
  - Zinc based NbE interpreter. Implementation of the Zinc machine
    extended with some ad hoc rules to do NbE. I am not actually sure that
    rules are correct, but they seem to be. Alas, its two times slower than
    PlainEval, so not worth it regardless. Perhaps maybe in C?
  
  - MarshalledTerm. This "marshals" term into a byte array and then evaluates
    the marshalled term. It also uses tricks from NestedEval - applications
    and abstractions are merged. This is roughly 20% faster than PlainEval.

  Some ideas I ruled out

  - Unrolling VApp into VApp1, VApp2, VApp3, etc in NestedEval. Didn't actually
    make a difference and in a normal NbE interpreter there would be a big
    spine instead.

  - Encoding (TVar v) variant as Ocaml Integer to save up on space. I tried this,
    but it slowed things down due to having to do double dispatch - first checking
    if something is a runtime integer, then dispatching on the actual runtime
    representation
*)

type tm = TLam of tm | TApp of tm * tm | TVar of int
type value = VLam of tm * value list | VNeu of int | VApp of value * value

let rec pp_tm (fmt : Format.formatter) (t : tm) : unit =
  match t with
  | TLam t -> Format.fprintf fmt "@[λ.@,%a@]" pp_tm t
  | TApp (t1, t2) -> Format.fprintf fmt "@[(%a)@ (%a)@]" pp_tm t1 pp_tm t2
  | TVar v -> Format.fprintf fmt "%i" v

open List

(* Plain NbE evaluation, nothing fancy *)
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

(* Some preprocessing to handle applications of different arities *)
module NestedEval = struct
  type ctm =
    | CTVar of int
    | CTApp1 of ctm * ctm
    | CTApp2 of ctm * ctm * ctm
    | CTApp3 of ctm * ctm * ctm * ctm
    | CTLam1 of ctm
    | CTLam2 of ctm
    | CTLam3 of ctm

  let rec compile : tm -> ctm = function
    | TVar i -> CTVar i
    | TApp (TApp (TApp (f, a1), a2), a3) ->
        CTApp3 (compile f, compile a1, compile a2, compile a3)
    | TApp (TApp (f, a1), a2) -> CTApp2 (compile f, compile a1, compile a2)
    | TApp (f, a1) -> CTApp1 (compile f, compile a1)
    | TLam (TLam (TLam t)) -> CTLam3 (compile t)
    | TLam (TLam t) -> CTLam2 (compile t)
    | TLam t -> CTLam1 (compile t)

  type value =
    | VLam1 of ctm * value list
    | VLam2 of ctm * value list
    | VLam3 of ctm * value list
    | VNeu of int
    (* Unwrapping VApps is not worth it practically since this will be a spine anyway*)
    | VApp of value * value

  let rec eval (t : ctm) (env : value list) : value =
    match t with
    | CTVar idx -> nth env idx
    | CTApp3 (f, a1, a2, a3) ->
        apply3 (eval f env) (eval a1 env) (eval a2 env) (eval a3 env)
    | CTApp2 (f, a1, a2) -> apply2 (eval f env) (eval a1 env) (eval a2 env)
    | CTApp1 (f, a1) -> apply1 (eval f env) (eval a1 env)
    | CTLam3 t -> VLam3 (t, env)
    | CTLam2 t -> VLam2 (t, env)
    | CTLam1 t -> VLam1 (t, env)

  and apply1 (f : value) (a : value) : value =
    match f with
    | VLam1 (fb, fenv) -> eval fb (a :: fenv)
    | VLam2 (fb, fenv) -> VLam1 (fb, a :: fenv)
    | VLam3 (fb, fenv) -> VLam2 (fb, a :: fenv)
    | v -> VApp (v, a)

  and apply2 (f : value) (a1 : value) (a2 : value) =
    match f with
    | VLam1 (fb, fenv) -> apply1 (eval fb (a1 :: fenv)) a2
    | VLam2 (fb, fenv) -> eval fb (a2 :: a1 :: fenv)
    | VLam3 (fb, fenv) -> VLam1 (fb, a2 :: a1 :: fenv)
    | f -> VApp (VApp (f, a1), a2)

  and apply3 (f : value) (a1 : value) (a2 : value) (a3 : value) =
    match f with
    | VLam1 (fb, fenv) -> apply2 (eval fb (a1 :: fenv)) a2 a3
    | VLam2 (fb, fenv) -> apply1 (eval fb (a2 :: a1 :: fenv)) a3
    | VLam3 (fb, fenv) -> eval fb (a3 :: a2 :: a1 :: fenv)
    | f -> VApp (VApp (VApp (f, a1), a2), a3)

  let rec quote (bindings : int) (v : value) : tm =
    match v with
    | VLam1 (t, env) ->
        TLam (quote (bindings + 1) (eval t (VNeu bindings :: env)))
    | VLam2 (t, env) ->
        TLam
          (TLam
             (quote (bindings + 2)
                (eval t (VNeu (bindings + 1) :: VNeu bindings :: env))))
    | VLam3 (t, env) ->
        TLam
          (TLam
             (TLam
                (quote (bindings + 3)
                   (eval t
                      (VNeu (bindings + 2)
                      :: VNeu (bindings + 1)
                      :: VNeu bindings :: env)))))
    | VApp (t1, t2) -> TApp (quote bindings t1, quote bindings t2)
    | VNeu level -> TVar (bindings - level - 1)

  let nf_compiled (t : ctm) : tm = quote 0 (eval t [])
  let nf (t : tm) : tm = quote 0 (eval (compile t) [])
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

(* NbE with Zinc machine. This version is actually two times slower than plain NbE interpreter. *)
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

(* Uhh, nothing to see here :^) *)
external set16u : bytes -> int -> int -> unit = "%caml_bytes_set16u"
external get16u : bytes -> int -> int = "%caml_bytes_get16u"

external caml_bytes_set32u : bytes -> int -> int32 -> unit
  = "%caml_bytes_set32u"

external caml_bytes_get32u : bytes -> int -> int32 = "%caml_bytes_get32u"

let get32u (b : bytes) (i : int) : int = Int32.to_int (caml_bytes_get32u b i)
[@@inline always]

let set32u (b : bytes) (i : int) (v : int) : unit =
  caml_bytes_set32u b i (Int32.of_int v)
[@@inline always]

(* Converting terms to byte sequences *)
module TermMarshal = struct
  let byte_var_boundary : int = 0xf8
  let far_var_marker : char = '\xf9'
  let app1_byte : char = '\xfa'
  let app2_byte : char = '\xfb'
  let app3_byte : char = '\xfc'
  let lam1_byte : char = '\xfd'
  let lam2_byte : char = '\xfe'
  let lam3_byte : char = '\xff'

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

  let write_uint32 (w : writer) (v : int) : unit =
    write w 4 (fun b i -> set32u b i v)

  let make_uint32_hole (w : writer) : int =
    let offset = w.offset in
    write_uint32 w 0;
    offset

  exception MarshallingError of string

  let fill_uint32_hole (w : writer) (hole : int) (v : int) : unit =
    if v > Int32.to_int Int32.max_int then
      raise (MarshallingError "can't skip over the term")
    else set32u w.bytes hole v

  let rec marshal (w : writer) (t : tm) : int =
    let rec go (w : writer) : tm -> unit = function
      | TApp (TApp (TApp (f, a1), a2), a3) ->
          let start_offset = w.offset in
          write_char w app3_byte;
          let a1_offset_hole = make_uint32_hole w in
          let a2_offset_hole = make_uint32_hole w in
          let a3_offset_hole = make_uint32_hole w in
          push w start_offset a1_offset_hole f;
          push w start_offset a2_offset_hole a1;
          push w start_offset a3_offset_hole a2;
          go w a3
      | TApp (TApp (f, a1), a2) ->
          let start_offset = w.offset in
          write_char w app2_byte;
          let a1_offset_hole = make_uint32_hole w in
          let a2_offset_hole = make_uint32_hole w in
          push w start_offset a1_offset_hole f;
          push w start_offset a2_offset_hole a1;
          go w a2
      | TApp (f, a1) ->
          let start_offset = w.offset in
          write_char w app1_byte;
          let a1_offset_hole = make_uint32_hole w in
          push w start_offset a1_offset_hole f;
          go w a1
      | TLam (TLam (TLam b)) ->
          write_char w lam3_byte;
          go w b
      | TLam (TLam b) ->
          write_char w lam2_byte;
          go w b
      | TLam b ->
          write_char w lam1_byte;
          go w b
      | TVar v ->
          if v <= byte_var_boundary then write_char w (char_of_int v)
          else if v < 65536 then (
            write_char w far_var_marker;
            write_uint32 w v)
          else raise (MarshallingError "variable too big")
    and push (w : writer) (start : int) (hole : int) (arg : tm) =
      go w arg;
      fill_uint32_hole w hole (w.offset - start)
    in

    let offset = w.offset in
    go w t;
    offset
end

module MarshalledEval = struct
  (* int in VLam represents byte offset into the buffer where marshalled term starts *)
  type value =
    | VLam1 of int * value list
    | VLam2 of int * value list
    | VLam3 of int * value list
    | VNeu of int
    | VApp of value * value

  let rec eval (b : bytes) (pc : int) (env : value list) : value =
    match Bytes.unsafe_get b pc with
    | '\xf9' ->
        (* Far variable access *)
        nth env (get32u b (pc + 1))
    | '\xfa' ->
        (* f a *)
        let f = eval b (pc + 5) env in
        let a = eval b (pc + get32u b (pc + 1)) env in
        apply1 b f a
    | '\xfb' ->
        (* f a1 a2 *)
        let f = eval b (pc + 9) env in
        let a1 = eval b (pc + get32u b (pc + 1)) env in
        let a2 = eval b (pc + get32u b (pc + 5)) env in
        apply2 b f a1 a2
    | '\xfc' ->
        (* f a1 a2 a3 *)
        let f = eval b (pc + 13) env in
        let a1 = eval b (pc + get32u b (pc + 1)) env in
        let a2 = eval b (pc + get32u b (pc + 5)) env in
        let a3 = eval b (pc + get32u b (pc + 9)) env in
        apply3 b f a1 a2 a3
    | '\xfd' ->
        (* \. b *)
        VLam1 (pc + 1, env)
    | '\xfe' ->
        (* \. \. b *)
        VLam2 (pc + 1, env)
    | '\xff' ->
        (* \. \. \. b *)
        VLam3 (pc + 1, env)
    | c ->
        (* Close variable access *)
        nth env (int_of_char c)

  and apply1 (b : bytes) (f : value) (a : value) : value =
    match f with
    | VLam1 (pc, env) -> eval b pc (a :: env)
    | VLam2 (pc, env) -> VLam1 (pc, a :: env)
    | VLam3 (pc, env) -> VLam2 (pc, a :: env)
    | v -> VApp (v, a)

  and apply2 (b : bytes) (f : value) (a1 : value) (a2 : value) =
    match f with
    | VLam1 (pc, env) -> apply1 b (eval b pc (a1 :: env)) a2
    | VLam2 (pc, env) -> eval b pc (a2 :: a1 :: env)
    | VLam3 (pc, env) -> VLam1 (pc, a2 :: a1 :: env)
    | f -> VApp (VApp (f, a1), a2)

  and apply3 (b : bytes) (f : value) (a1 : value) (a2 : value) (a3 : value) =
    match f with
    | VLam1 (pc, env) -> apply2 b (eval b pc (a1 :: env)) a2 a3
    | VLam2 (pc, env) -> apply1 b (eval b pc (a2 :: a1 :: env)) a3
    | VLam3 (pc, env) -> eval b pc (a3 :: a2 :: a1 :: env)
    | f -> VApp (VApp (VApp (f, a1), a2), a3)

  let rec quote (b : bytes) (bindings : int) : value -> tm = function
    | VNeu lvl -> TVar (bindings - lvl - 1)
    | VApp (v1, v2) -> TApp (quote b bindings v1, quote b bindings v2)
    | VLam1 (pc, env) ->
        TLam (quote b (bindings + 1) (eval b pc (VNeu bindings :: env)))
    | VLam2 (pc, env) ->
        TLam
          (TLam
             (quote b (bindings + 2)
                (eval b pc (VNeu (bindings + 1) :: VNeu bindings :: env))))
    | VLam3 (pc, env) ->
        TLam
          (TLam
             (TLam
                (quote b (bindings + 3)
                   (eval b pc
                      (VNeu (bindings + 2)
                      :: VNeu (bindings + 1)
                      :: VNeu bindings :: env)))))

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
  let rec go acc = function
    | 0 -> acc
    | n ->
        Gc.full_major ();
        Format.printf "Running '%s' (%i runs remaining)\n@?" name n;
        let startT = Sys.time () in
        let actual = f n in
        let endT = Sys.time () in
        if actual <> expected then (
          Format.printf
            "Incorrect result for '%s'@\nexpected: @[%a@]@\nactual: @[%a@]\n@?"
            name pp_tm expected pp_tm actual;
          exit 1)
        else go ((endT -. startT) :: acc) (n - 1)
  in
  (* Some time for CPU to calm down. It's fine if this returns 0 *)
  let _ =
    if Sys.win32 then Sys.command "timeout /t 5" else Sys.command "sleep 5"
  in
  let times = List.fast_sort Float.compare (go [] runs) in
  let median =
    if Int.rem runs 2 = 0 then
      (nth times (runs / 2) +. nth times ((runs / 2) - 1)) /. 2.0
    else nth times (runs / 2)
  in
  Format.printf "Median for '%s' is %f seconds\n@?" name median

let try_all () =
  benchmark "plain NbE (1000 - 1000)" (TLam (TLam (TVar 0))) ~runs:10 (fun _ ->
      PlainEval.nf (testTerm 1000));
  benchmark "nested NbE (1000 - 1000)" (TLam (TLam (TVar 0))) ~runs:10 (fun _ ->
      NestedEval.nf (testTerm 1000));
  benchmark "NbE over marshalled terms (1000 - 1000)" (TLam (TLam (TVar 0)))
    ~runs:10 (fun _ -> MarshalledEval.nf (testTerm 1000));
  benchmark "cps NbE (1000 - 1000)" ~runs:10 (TLam (TLam (TVar 0))) (fun _ ->
      CPSEval.nf (testTerm 1000));
  benchmark "1000 - 1000 on Zinc machine" (TLam (TLam (TVar 0))) (fun _ ->
      Zinc.nf (testTerm 1000));
  benchmark "plain NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      PlainEval.nf (testTerm 3000));
  benchmark "nested NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      PlainEval.nf (testTerm 3000));
  benchmark "NbE over marshalled terms (3000 - 3000)" (TLam (TLam (TVar 0)))
    (fun _ -> MarshalledEval.nf (testTerm 3000));
  benchmark "cps NbE (3000 - 3000)" (TLam (TLam (TVar 0))) (fun _ ->
      CPSEval.nf (testTerm 3000));
  benchmark "3000 - 3000 on Zinc machine" (TLam (TLam (TVar 0))) (fun _ ->
      Zinc.nf (testTerm 3000));
  benchmark "plain NbE (7000 - 7000)" (TLam (TLam (TVar 0))) ~runs:3 (fun _ ->
      PlainEval.nf (testTerm 7000));
  benchmark "nested NbE (7000 - 7000)" (TLam (TLam (TVar 0))) ~runs:3 (fun _ ->
      PlainEval.nf (testTerm 7000));
  benchmark "NbE over marshalled terms (7000 - 7000)" (TLam (TLam (TVar 0)))
    ~runs:3 (fun _ -> MarshalledEval.nf (testTerm 7000))

let huge () =
  benchmark "plain NbE (10000 - 10000)" (TLam (TLam (TVar 0))) ~runs:10
    (fun _ -> Sys.opaque_identity (PlainEval.nf (testTerm 10000)));
  benchmark "nested NbE (10000 - 10000)" (TLam (TLam (TVar 0))) ~runs:10
    (fun _ -> Sys.opaque_identity (NestedEval.nf (testTerm 10000)));
  benchmark "NbE over marshalled terms (10000 - 10000)" (TLam (TLam (TVar 0)))
    ~runs:10 (fun _ -> Sys.opaque_identity (MarshalledEval.nf (testTerm 10000)))

let many_smol () =
  let term = testTerm 200 in
  let compiled = NestedEval.compile term in
  benchmark "plain NbE (200 - 200) 1000 times" (TLam (TLam (TVar 0))) ~runs:5
    (fun _ ->
      let res = ref None in
      for _ = 0 to 1000 do
        res := Sys.opaque_identity (Some (PlainEval.nf term))
      done;
      Option.get !res);
  benchmark "plain NbE (200 - 200) 1000 times" (TLam (TLam (TVar 0))) ~runs:5
    (fun _ ->
      let res = ref None in
      for _ = 0 to 1000 do
        res := Sys.opaque_identity (Some (NestedEval.nf_compiled compiled))
      done;
      Option.get !res)

let tiny () =
  let term = testTerm 20 in
  let compiled = NestedEval.compile term in
  benchmark "plain NbE (20 - 20) 100000 times" (TLam (TLam (TVar 0))) ~runs:5
    (fun _ ->
      let res = ref None in
      for _ = 0 to 100000 do
        res := Sys.opaque_identity (Some (PlainEval.nf term))
      done;
      Option.get !res);
  benchmark "plain NbE (20 - 20) 100000 times" (TLam (TLam (TVar 0))) ~runs:5
    (fun _ ->
      let res = ref None in
      for _ = 0 to 100000 do
        res := Sys.opaque_identity (Some (NestedEval.nf_compiled compiled))
      done;
      Option.get !res)

let () = huge ()
