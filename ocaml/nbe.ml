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
  exception MarshallingError of string

  let byte_var_boundary : int = 0xe8
  let short_var_marker : char = '\xe9'
  let long_var_marker : char = '\xea'
  let vsapp1s_byte : char = '\xeb'
  let vsapp2s_byte : char = '\xec'
  let vsapp3s_byte : char = '\xed'
  let vsapp1l_byte : char = '\xee'
  let vsapp2l_byte : char = '\xef'
  let vsapp3l_byte : char = '\xf0'
  let vapp1s_byte : char = '\xf1'
  let vapp2s_byte : char = '\xf2'
  let vapp3s_byte : char = '\xf3'
  let vapp1l_byte : char = '\xf4'
  let vapp2l_byte : char = '\xf5'
  let vapp3l_byte : char = '\xf6'
  let app1s_byte : char = '\xf7'
  let app2s_byte : char = '\xf8'
  let app3s_byte : char = '\xf9'
  let app1l_byte : char = '\xfa'
  let app2l_byte : char = '\xfb'
  let app3l_byte : char = '\xfc'
  let lam1_byte : char = '\xfd'
  let lam2_byte : char = '\xfe'
  let lam3_byte : char = '\xff'

  type writer = { mutable bytes : bytes; mutable offset : int }

  let new_writer () : writer = { bytes = Bytes.create 128; offset = 0 }

  let grow (w : writer) : unit =
    w.bytes <- Bytes.extend w.bytes 0 (Bytes.length w.bytes)

  let rec ensure_capacity (w : writer) (min : int) : unit =
    let remaining = Bytes.length w.bytes - w.offset in
    if remaining < min then (
      grow w;
      ensure_capacity w min)
    else ()

  let write_char (w : writer) (c : char) : unit =
    Bytes.unsafe_set w.bytes w.offset c;
    w.offset <- w.offset + 1

  let write_uint16 (w : writer) (v : int) : unit =
    set16u w.bytes w.offset v;
    w.offset <- w.offset + 2

  let write_uint32 (w : writer) (v : int) : unit =
    set32u w.bytes w.offset v;
    w.offset <- w.offset + 4

  type tm_layout =
    | InlineVar of char (* 1 byte inline ref *)
    | ShortVar of int (* \xe9 + 2 bytes de brujin index *)
    | LongVar of int (* \xea + 4 bytes de brujin index (who would need more?) *)
    (* \xeb + 2x 2 byte args *)
    | ShortVarsOnlyApp1 of int * int
    (* \xec + 3x 2 byte args *)
    | ShortVarsOnlyApp2 of int * int * int
    (* \xed + 4x 2 byte args *)
    | ShortVarsOnlyApp3 of int * int * int * int
    (* \xee + 2x 4 byte variable indices *)
    | LongVarsOnlyApp1 of int * int
    (* \xef + 3x 4 byte variable indices *)
    | LongVarsOnlyApp2 of int * int * int
    (* \xf0 + 4x 4 byte variable indices *)
    | LongVarsOnlyApp3 of int * int * int * int
    (* \xf1 + 2 byte variable index + [[a1]] *)
    | ShortVarApp1 of int * tm_layout
    (* \xf2 + 2 byte variable index + 2 byte offset + [[a1]] + [[a2]] *)
    | ShortVarApp2 of int * int * tm_layout * tm_layout
    (* \xf3 + 2 byte variable index + 2x 2 byte offsets + [[a1]] + [[a2]] + [[a3]] *)
    | ShortVarApp3 of int * int * int * tm_layout * tm_layout * tm_layout
    (* \xf4 + 4 byte variable index + [[a1]] *)
    | LongVarApp1 of int * tm_layout
    (* \xf5 + 4 byte variable index + 4 byte offset + [[a1]] + [[a2]] *)
    | LongVarApp2 of int * int * tm_layout * tm_layout
    (* \xf3 + 4 byte variable index + 2x 4 byte offsets + [[a1]] + [[a2]] + [[a3]] *)
    | LongVarApp3 of int * int * int * tm_layout * tm_layout * tm_layout
    (* \xf7 + 2 byte offset of a1 + [[f]] + [[a1]] *)
    | ShortApp1 of int * tm_layout * tm_layout
    (* \xf8 + 2 byte offsets of a1 and a2 + [[f]] + [[a1]] + [[a2]] *)
    | ShortApp2 of int * int * tm_layout * tm_layout * tm_layout
    (* \xf9 + 2 byte offsets of a1, a2, and a3 + [[f]] + [[a1]] + [[a2]] + [[a3]] *)
    | ShortApp3 of
        int * int * int * tm_layout * tm_layout * tm_layout * tm_layout
    (* \xfa + 4 byte offset of a1 + [[f]] + [[a1]] *)
    | LongApp1 of int * tm_layout * tm_layout
    (* \xfb + 4 byte offsets of a1 and a2 + [[f]] + [[a1]] + [[a2]] *)
    | LongApp2 of int * int * tm_layout * tm_layout * tm_layout
    (* \xfc + 4 byte offsets of a1, a2, and a3 + [[f]] + [[a1]] + [[a2]] + [[a3]] *)
    | LongApp3 of
        int * int * int * tm_layout * tm_layout * tm_layout * tm_layout
    (* \xfd + [[b]] - lambda accepting at least one argument *)
    | Lam1Mark of tm_layout
    (* \xfe + [[b]] - lambda accepting at least two arguments *)
    | Lam2Mark of tm_layout
    (* \xff + [[b]] - lambda accepting at least three arguments *)
    | Lam3Mark of tm_layout

  let rec build_layout (size : int ref) : tm -> tm_layout = function
    | TVar i ->
        if i <= byte_var_boundary then (
          incr size;
          InlineVar (Char.chr i))
        else if i <= 32767 then (
          (* TODO - use unsigned repr *)
          size := !size + 3;
          ShortVar i)
        else (
          assert (!size <= Int32.to_int Int32.max_int);
          size := !size + 5;
          LongVar i)
    | TApp (TApp (TApp (TVar v1, TVar v2), TVar v3), TVar v4) ->
        if v1 <= 32767 && v2 <= 32767 && v3 <= 32767 && v4 <= 32767 then (
          size := !size + 9;
          ShortVarsOnlyApp3 (v1, v2, v3, v4))
        else (
          size := !size + 17;
          LongVarsOnlyApp3 (v1, v2, v3, v4))
    | TApp (TApp (TVar v1, TVar v2), TVar v3) ->
        if v1 <= 32767 && v2 <= 32767 && v3 <= 32767 then (
          size := !size + 7;
          ShortVarsOnlyApp2 (v1, v2, v3))
        else (
          size := !size + 13;
          LongVarsOnlyApp2 (v1, v2, v3))
    | TApp (TVar v1, TVar v2) ->
        if v1 <= 32767 && v2 <= 32767 then (
          size := !size + 5;
          ShortVarsOnlyApp1 (v1, v2))
        else (
          size := !size + 9;
          LongVarsOnlyApp1 (v1, v2))
    | TApp (TApp (TApp (TVar v, a1), a2), a3) ->
        let size_before = !size in
        let la1 = build_layout size a1 in
        let a2_offset = !size - size_before in
        let la2 = build_layout size a2 in
        let a3_offset = !size - size_before in
        let la3 = build_layout size a3 in
        if v <= 32767 && a3_offset <= 32767 - 7 then (
          (* 3 short fields and 1 header byte *)
          size := !size + 7;
          ShortVarApp3 (v, a2_offset + 7, a3_offset + 7, la1, la2, la3))
        else (
          size := !size + 13;
          LongVarApp3 (v, a2_offset + 13, a3_offset + 13, la1, la2, la3))
    | TApp (TApp (TVar v, a1), a2) ->
        let size_before = !size in
        let la1 = build_layout size a1 in
        let a2_offset = !size - size_before in
        let la2 = build_layout size a2 in
        if v <= 32767 && a2_offset <= 32767 - 5 then (
          (* 2 short fields and 1 header byte *)
          size := !size + 5;
          ShortVarApp2 (v, a2_offset + 5, la1, la2))
        else (
          size := !size + 9;
          LongVarApp2 (v, a2_offset + 9, la1, la2))
    | TApp (TVar v, a1) ->
        let la1 = build_layout size a1 in
        if v <= 32767 then (
          size := !size + 3;
          ShortVarApp1 (v, la1))
        else (
          size := !size + 5;
          LongVarApp1 (v, la1))
    | TApp (TApp (TApp (f, a1), a2), a3) ->
        let size_before = !size in
        let lf = build_layout size f in
        let a1_offset = !size - size_before in
        let la1 = build_layout size a1 in
        let a2_offset = !size - size_before in
        let la2 = build_layout size a2 in
        let a3_offset = !size - size_before in
        let la3 = build_layout size a3 in
        if a3_offset <= 32767 - 7 then (
          (* 3 short fields and 1 header byte *)
          size := !size + 7;
          ShortApp3
            (a1_offset + 7, a2_offset + 7, a3_offset + 7, lf, la1, la2, la3))
        else (
          size := !size + 13;
          LongApp3
            (a1_offset + 13, a2_offset + 13, a3_offset + 13, lf, la1, la2, la3))
    | TApp (TApp (f, a1), a2) ->
        let size_before = !size in
        let lf = build_layout size f in
        let a1_offset = !size - size_before in
        let la1 = build_layout size a1 in
        let a2_offset = !size - size_before in
        let la2 = build_layout size a2 in
        if a2_offset <= 32767 - 5 then (
          (* 2 short fields and 1 header byte *)
          size := !size + 5;
          ShortApp2 (a1_offset + 5, a2_offset + 5, lf, la1, la2))
        else (
          size := !size + 9;
          LongApp2 (a1_offset + 9, a2_offset + 9, lf, la1, la2))
    | TApp (f, a1) ->
        let size_before = !size in
        let lf = build_layout size f in
        let a1_offset = !size - size_before in
        let la1 = build_layout size a1 in
        if a1_offset <= 32767 - 3 then (
          (* 1 short field and 1 header byte *)
          size := !size + 3;
          ShortApp1 (a1_offset + 3, lf, la1))
        else (
          size := !size + 5;
          LongApp1 (a1_offset + 5, lf, la1))
    | TLam (TLam (TLam t)) ->
        incr size;
        Lam3Mark (build_layout size t)
    | TLam (TLam t) ->
        incr size;
        Lam2Mark (build_layout size t)
    | TLam t ->
        incr size;
        Lam1Mark (build_layout size t)

  let rec marshal (w : writer) (t : tm) : int =
    let write_hdr1 (f : writer -> int -> unit) (w : writer) (c : char)
        (h1 : int) : unit =
      write_char w c;
      f w h1
        [@@inline always]
    in
    let write_hdr2 (f : writer -> int -> unit) (w : writer) (c : char)
        (h1 : int) (h2 : int) : unit =
      write_char w c;
      f w h1;
      f w h2
        [@@inline always]
    in

    let write_hdr3 (f : writer -> int -> unit) (w : writer) (c : char)
        (h1 : int) (h2 : int) (h3 : int) : unit =
      write_char w c;
      f w h1;
      f w h2;
      f w h3
        [@@inline always]
    in

    let write_hdr4 (f : writer -> int -> unit) (w : writer) (c : char)
        (h1 : int) (h2 : int) (h3 : int) (h4 : int) : unit =
      write_char w c;
      f w h1;
      f w h2;
      f w h3;
      f w h4
        [@@inline always]
    in

    let rec go (w : writer) : tm_layout -> unit = function
      | InlineVar c -> write_char w c
      | ShortVar i -> write_hdr1 write_uint16 w short_var_marker i
      | LongVar i -> write_hdr1 write_uint32 w short_var_marker i
      | ShortVarsOnlyApp1 (v1, v2) ->
          write_hdr2 write_uint16 w vsapp1s_byte v1 v2
      | ShortVarsOnlyApp2 (v1, v2, v3) ->
          write_hdr3 write_uint16 w vsapp2s_byte v1 v2 v3
      | ShortVarsOnlyApp3 (v1, v2, v3, v4) ->
          write_hdr4 write_uint16 w vsapp3s_byte v1 v2 v3 v4
      | LongVarsOnlyApp1 (v1, v2) ->
          write_hdr2 write_uint32 w vsapp1l_byte v1 v2
      | LongVarsOnlyApp2 (v1, v2, v3) ->
          write_hdr3 write_uint32 w vsapp2l_byte v1 v2 v3
      | LongVarsOnlyApp3 (v1, v2, v3, v4) ->
          write_hdr4 write_uint32 w vsapp3l_byte v1 v2 v3 v4
      | ShortVarApp1 (fv, a1) ->
          write_hdr1 write_uint16 w vapp1s_byte fv;
          go w a1
      | ShortVarApp2 (fv, a1off, a1, a2) ->
          write_hdr2 write_uint16 w vapp2s_byte fv a1off;
          go2 w a1 a2
      | ShortVarApp3 (fv, a1off, a2off, a1, a2, a3) ->
          write_hdr3 write_uint16 w vapp3s_byte fv a1off a2off;
          go3 w a1 a2 a3
      | LongVarApp1 (fv, a1) ->
          write_hdr1 write_uint32 w vapp1l_byte fv;
          go w a1
      | LongVarApp2 (fv, a1off, a1, a2) ->
          write_hdr2 write_uint32 w vapp2l_byte fv a1off;
          go2 w a1 a2
      | LongVarApp3 (fv, a1off, a2off, a1, a2, a3) ->
          write_hdr3 write_uint32 w vapp3l_byte fv a1off a2off;
          go3 w a1 a2 a3
      | ShortApp1 (a1off, f, a1) ->
          write_hdr1 write_uint16 w app1s_byte a1off;
          go2 w f a1
      | ShortApp2 (a1off, a2off, f, a1, a2) ->
          write_hdr2 write_uint16 w app2s_byte a1off a2off;
          go3 w f a1 a2
      | ShortApp3 (a1off, a2off, a3off, f, a1, a2, a3) ->
          write_hdr3 write_uint16 w app3s_byte a1off a2off a3off;
          go4 w f a1 a2 a3
      | LongApp1 (a1off, f, a1) ->
          write_hdr1 write_uint32 w app1l_byte a1off;
          go2 w f a1
      | LongApp2 (a1off, a2off, f, a1, a2) ->
          write_hdr2 write_uint32 w app2l_byte a1off a2off;
          go3 w f a1 a2
      | LongApp3 (a1off, a2off, a3off, f, a1, a2, a3) ->
          write_hdr3 write_uint16 w app3l_byte a1off a2off a3off;
          go4 w f a1 a2 a3
      | Lam1Mark b -> char_and_go w lam1_byte b
      | Lam2Mark b -> char_and_go w lam2_byte b
      | Lam3Mark b -> char_and_go w lam3_byte b
    and go2 (w : writer) (t1 : tm_layout) (t2 : tm_layout) : unit =
      go w t1;
      go w t2
    and go3 (w : writer) (t1 : tm_layout) (t2 : tm_layout) (t3 : tm_layout) :
        unit =
      go w t1;
      go w t2;
      go w t3
    and go4 (w : writer) (t1 : tm_layout) (t2 : tm_layout) (t3 : tm_layout)
        (t4 : tm_layout) : unit =
      go w t1;
      go w t2;
      go w t3;
      go w t4
    and char_and_go (w : writer) (c : char) (t : tm_layout) =
      write_char w c;
      go w t
    in

    let offset = w.offset in
    let size_ref = ref 0 in
    let layout = build_layout size_ref t in
    ensure_capacity w !size_ref;
    go w layout;
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
    | '\xe9' ->
        (* 16-bit indexed variable access *)
        nth env (get16u b (pc + 1))
    | '\xea' ->
        (* 32-bit indexed variable access *)
        nth env (get32u b (pc + 1))
    | '\xeb' ->
        (* (var f) (var a1) with short offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = nth env (get16u b (pc + 3)) in
        apply1 b f a1
    | '\xec' ->
        (* (var f) (var a1) (var a2) with short offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = nth env (get16u b (pc + 3)) in
        let a2 = nth env (get16u b (pc + 5)) in
        apply2 b f a1 a2
    | '\xed' ->
        (* (var f) (var a1) (var a2) (var a3) with short offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = nth env (get16u b (pc + 3)) in
        let a2 = nth env (get16u b (pc + 5)) in
        let a3 = nth env (get16u b (pc + 7)) in
        apply3 b f a1 a2 a3
    | '\xee' ->
        (* (var f) (var a1) with long offsets *)
        let f = nth env (get32u b (pc + 1)) in
        let a1 = nth env (get32u b (pc + 5)) in
        apply1 b f a1
    | '\xef' ->
        (* (var f) (var a1) (var a2) with long offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = nth env (get16u b (pc + 5)) in
        let a2 = nth env (get16u b (pc + 9)) in
        apply2 b f a1 a2
    | '\xf0' ->
        (* (var f) (var a1) (var a2) (var a3) with long offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = nth env (get16u b (pc + 5)) in
        let a2 = nth env (get16u b (pc + 9)) in
        let a3 = nth env (get16u b (pc + 13)) in
        apply3 b f a1 a2 a3
    | '\xf1' ->
        (* (var v) a1 with short offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = eval b (pc + 3) env in
        apply1 b f a1
    | '\xf2' ->
        (* (var v) a1 a2 with short offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = eval b (pc + 5) env in
        let a2 = eval b (pc + get16u b (pc + 3)) env in
        apply2 b f a1 a2
    | '\xf3' ->
        (* (var v) a1 a2 a3 with short offsets *)
        let f = nth env (get16u b (pc + 1)) in
        let a1 = eval b (pc + 7) env in
        let a2 = eval b (pc + get16u b (pc + 3)) env in
        let a3 = eval b (pc + get16u b (pc + 5)) env in
        apply3 b f a1 a2 a3
    | '\xf4' ->
        (* (var v) a1 with long offsets *)
        let f = nth env (get32u b (pc + 1)) in
        let a1 = eval b (pc + 5) env in
        apply1 b f a1
    | '\xf5' ->
        (* (var v) a1 a2 with long offsets *)
        let f = nth env (get32u b (pc + 1)) in
        let a1 = eval b (pc + 9) env in
        let a2 = eval b (pc + get32u b (pc + 5)) env in
        apply2 b f a1 a2
    | '\xf6' ->
        (* (var v) a1 a2 a3 with long offsets *)
        let f = nth env (get32u b (pc + 1)) in
        let a1 = eval b (pc + 13) env in
        let a2 = eval b (pc + get32u b (pc + 5)) env in
        let a3 = eval b (pc + get32u b (pc + 9)) env in
        apply3 b f a1 a2 a3
    | '\xf7' ->
        (* f a1 with short offsets *)
        let f = eval b (pc + 3) env in
        let a1 = eval b (pc + get16u b (pc + 1)) env in
        apply1 b f a1
    | '\xf8' ->
        (* f a1 a2 with short offsets *)
        let f = eval b (pc + 5) env in
        let a1 = eval b (pc + get16u b (pc + 1)) env in
        let a2 = eval b (pc + get16u b (pc + 3)) env in
        apply2 b f a1 a2
    | '\xf9' ->
        (* f a1 a2 a3 with short offsets *)
        let f = eval b (pc + 7) env in
        let a1 = eval b (pc + get16u b (pc + 1)) env in
        let a2 = eval b (pc + get16u b (pc + 3)) env in
        let a3 = eval b (pc + get16u b (pc + 5)) env in
        apply3 b f a1 a2 a3
    | '\xfa' ->
        (* f a1 with long offsets *)
        let f = eval b (pc + 5) env in
        let a1 = eval b (pc + get32u b (pc + 1)) env in
        apply1 b f a1
    | '\xfb' ->
        (* f a1 a2 with long offsets *)
        let f = eval b (pc + 9) env in
        let a1 = eval b (pc + get32u b (pc + 1)) env in
        let a2 = eval b (pc + get32u b (pc + 5)) env in
        apply2 b f a1 a2
    | '\xfc' ->
        (* f a1 a2 a3 with long offsets *)
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

  and apply1 (b : bytes) (f : value) (a1 : value) : value =
    match f with
    | VLam1 (pc, env) -> eval b pc (a1 :: env)
    | VLam2 (pc, env) -> VLam1 (pc, a1 :: env)
    | VLam3 (pc, env) -> VLam2 (pc, a1 :: env)
    | f -> VApp (f, a1)

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

let huge n =
  benchmark "NbE over marshalled terms (10000 - 10000)" (TLam (TLam (TVar 0)))
    ~runs:n (fun _ -> Sys.opaque_identity (MarshalledEval.nf (testTerm 10000)));
  benchmark "plain NbE (10000 - 10000)" (TLam (TLam (TVar 0))) ~runs:n (fun _ ->
      Sys.opaque_identity (PlainEval.nf (testTerm 10000)));
  benchmark "nested NbE (10000 - 10000)" (TLam (TLam (TVar 0))) ~runs:n
    (fun _ -> Sys.opaque_identity (NestedEval.nf (testTerm 10000)))

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

let () = huge 20
