(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*               Jeremy Yallop, University of Cambridge                   *)
(*                                                                        *)
(*   Copyright 2017 Jeremy Yallop                                         *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Asttypes
open Typedtree
open Types

[@@@warning "+4"]

exception Illegal_expr

module Env' = Env
module Rec_context =
struct
  type mode =
      Dereferenced
    (** [Dereferenced] indicates that the value (not just the address) of a
        variable is accessed, or that an expression needs to be evaluated
        and accessed. *)

    | Guarded
    (** [Guarded] indicates that the address of a variable is used in a
        guarded context, i.e. under a constructor, or stored in a closure.
        An expression is [Guarded] the address of its value is used in a
        guarded context.*)

    | Delayed
    (** [Delayed] indicates that an expression has its evaluation delayed,
        i.e it is placed in a function or it is lazily evaluated.  A variable
        is delayed it is is placed in such an expression. *)

    | Unused
    (** [Unused] indicates that a variable is not used in an expression. *)

    | Unguarded
    (** [Unguarded] indicates that the address of a variable is used in an
        unguarded context, i.e. not under a constructor. *)

  (* Returns the most conservative mode of the two arguments. *)
  let prec m m' =
    match m, m' with
    | Dereferenced, _
    | _, Dereferenced -> Dereferenced
    | Unguarded, _
    | _, Unguarded -> Unguarded
    | Guarded, _
    | _, Guarded -> Guarded
    | Delayed, _
    | _, Delayed -> Delayed
    | _ -> Unused

  (* Suppose that a variable x is used with the mode m' in an expression
     that is used with mode m in a more global context.
     (compos m m') is the mode of x in this global context. *)
  let compos m m' = match m, m' with
    | Unused, _
    | _, Unused -> failwith "Not defined."
    | Dereferenced, _ -> Dereferenced
    | Delayed, _ -> Delayed
    | m, Unguarded -> m
    | Unguarded, m'
    | Guarded, m' -> m'

  (** let_in m_loc m_glob:
      in the expression let x = e in e', if x is used in mode m_loc in e 'and
      e' is used m_glob, let_in m_loc m_glob returns the mode in which e must
      be evaluated. *)
  let let_in m_loc m_glob =
    compos m_glob (prec m_loc Guarded)

  module Env :
  sig
    type t

    val single : Ident.t -> mode -> t
    (** Create an environment with a single identifier used with a given mode.
    *)

    val empty : t
    (** An environment with no used identifiers. *)

    val find : t -> Ident.t -> mode
    (** Find the mode of an indentifier in an environment.  The default mode is
        Unused. *)

    val unguarded : t -> Ident.t list
    (** The list of identifiers that are used in an unguarded context *)

    val dependent : t -> Ident.t list
    (** The list of all used identifiers *)

    val join : t -> t -> t

    val remove_list : Ident.t list -> t -> t
    (* Remove all the variables of a list from an environment. *)
  end =
  struct
    module M = Map.Make(Ident)

    (** A "t" maps each rec-bound variable to an access status *)
    type t = mode M.t

    let find (tbl: t) (id: Ident.t) =
      try M.find id tbl with Not_found -> Unused

    let join (x: t) (y: t) =
      M.fold
        (fun (id: Ident.t) (v: mode) (tbl: t) ->
           let v' = find tbl id in
           M.add id (prec v v') tbl)
        x y

    let single id mode = M.add id mode M.empty

    let empty = M.empty

    let list_matching p t =
      let r = ref [] in
      M.iter (fun id v -> if p v then r := id :: !r) t;
      !r

    let unguarded =
      list_matching (function Unguarded | Dereferenced -> true | _ -> false)

    let dependent =
      list_matching (function _ -> true)

    let remove_list l env =
      List.fold_left (fun e x -> M.remove x e) env l
  end
end

open Rec_context

let is_ref : Types.value_description -> bool = function
  | { Types.val_kind =
        Types.Val_prim { Primitive.prim_name = "%makemutable";
                          prim_arity = 1 } } ->
        true
  | _ -> false

let scrape env ty =
  (Ctype.repr (Ctype.expand_head_opt env (Ctype.correct_levels ty))).desc

let array_element_kind env ty =
  match scrape env ty with
  | Tvar _ | Tunivar _ ->
      `Pgenarray
  | Tconstr(p, _, _) ->
      if Path.same p Predef.path_int || Path.same p Predef.path_char then
        `Pintarray
      else if Path.same p Predef.path_float then
        if Config.flat_float_array then `Pfloatarray else `Paddrarray
      else if Path.same p Predef.path_string
            || Path.same p Predef.path_array
            || Path.same p Predef.path_nativeint
            || Path.same p Predef.path_int32
            || Path.same p Predef.path_int64 then
        `Paddrarray
      else begin
        try
          match Env'.find_type p env with
            {type_kind = Type_abstract} ->
              `Pgenarray
          | {type_kind = Type_variant cstrs}
            when List.for_all (fun c -> c.Types.cd_args = Types.Cstr_tuple [])
                cstrs ->
              `Pintarray
          | {type_kind = _} ->
              `Paddrarray
        with Not_found ->
          (* This can happen due to e.g. missing -I options,
              causing some .cmi files to be unavailable.
              Maybe we should emit a warning. *)
          `Pgenarray
      end
  | _ ->
      `Paddrarray

let array_type_kind env ty =
  match scrape env ty with
  | Tconstr(p, [elt_ty], _) | Tpoly({desc = Tconstr(p, [elt_ty], _)}, _)
    when Path.same p Predef.path_array ->
      array_element_kind env elt_ty
  | _ ->
      (* This can happen with e.g. Obj.field *)
      `Pgenarray

let array_kind exp = array_type_kind exp.exp_env exp.exp_type

(*
let has_concrete_element_type : Typedtree.expression -> bool =
  fun e -> array_kind e <> `Pgenarray
  *)

(* See the note on abstracted arguments in the documentation for
    Typedtree.Texp_apply *)
let is_abstracted_arg : arg_label * expression option -> bool = function
  | (_, None) -> true
  | (_, Some _) -> false

type sd = Static | Dynamic

let classify_expression : Typedtree.expression -> sd =
  (* We need to keep track of the size of expressions
      bound by local declarations, to be able to predict
      the size of variables. Compare:

        let rec r =
          let y = fun () -> r ()
          in y

      and

        let rec r =
          let y = if Random.bool () then ignore else fun () -> r ()
          in y

    In both cases the final adress of `r` must be known before `y` is compiled,
    and this is only possible if `r` has a statically-known size.

    The first definition can be allowed (`y` has a statically-known
    size) but the second one is unsound (`y` has no statically-known size).
  *)
  let rec classify_expression env e = match e.exp_desc with
    (* binding and variable cases *)
    | Texp_let (rec_flag, vb, e) ->
        let env = classify_value_bindings rec_flag env vb in
        classify_expression env e
    | Texp_ident (path, _, _) ->
        classify_path env path

    (* non-binding cases *)
    | Texp_letmodule (_, _, _, e)
    | Texp_sequence (_, e)
    | Texp_letexception (_, e) ->
        classify_expression env e

    | Texp_construct (_, {cstr_tag = Cstr_unboxed}, [e]) ->
        classify_expression env e
    | Texp_construct _ ->
        Static

    | Texp_record { representation = Record_unboxed _;
                    fields = [| _, Overridden (_,e) |] } ->
        classify_expression env e
    | Texp_record _ ->
        Static

    | Texp_apply ({exp_desc = Texp_ident (_, _, vd)}, _)
      when is_ref vd ->
        Static
    | Texp_apply (_,args)
      when List.exists is_abstracted_arg args ->
        Static
    | Texp_apply _ ->
        Dynamic

    | Texp_for _
    | Texp_constant _
    | Texp_new _
    | Texp_instvar _
    | Texp_tuple _
    | Texp_array _
    | Texp_variant _
    | Texp_setfield _
    | Texp_while _
    | Texp_setinstvar _
    | Texp_pack _
    | Texp_object _
    | Texp_function _
    | Texp_lazy _
    | Texp_unreachable
    | Texp_extension_constructor _ ->
        Static

    | Texp_match _
    | Texp_ifthenelse _
    | Texp_send _
    | Texp_field _
    | Texp_assert _
    | Texp_try _
    | Texp_override _ ->
        Dynamic
  and classify_value_bindings rec_flag env bindings =
    (* We use a non-recursive classification, classifying each
        binding with respect to the old environment
        (before all definitions), even if the bindings are recursive.

        Note: computing a fixpoint in some way would be more
        precise, as the following could be allowed:

          let rec topdef =
            let rec x = y and y = fun () -> topdef ()
            in x
    *)
    ignore rec_flag;
    let old_env = env in
    let add_value_binding env vb =
      match vb.vb_pat.pat_desc with
      | Tpat_var (id, _loc) ->
          let size = classify_expression old_env vb.vb_expr in
          Ident.add id size env
      | _ ->
          (* Note: we don't try to compute any size for complex patterns *)
          env
    in
    List.fold_left add_value_binding env bindings
  and classify_path env = function
    | Path.Pident x ->
        begin
          try Ident.find_same x env
          with Not_found ->
            (* an identifier will be missing from the map if either:
                - it is a non-local identifier
                  (bound outside the letrec-binding we are analyzing)
                - or it is bound by a complex (let p = e in ...) local binding
                - or it is bound within a module (let module M = ... in ...)
                  that we are not traversing for size computation

                For non-local identifiers it might be reasonable (although
                not completely clear) to consider them Static (they have
                already been evaluated), but for the others we must
                under-approximate with Dynamic.

                This could be fixed by a more complete implementation.
            *)
            Dynamic
        end
    | Path.Pdot _ | Path.Papply _ ->
        (* local modules could have such paths to local definitions;
            classify_expression could be extend to compute module
            shapes more precisely *)
        Dynamic
  in classify_expression Ident.empty

(* TODO: it's ugly *)
type pattern_info =
  | NonDestructuring of Ident.t option
  | Destructuring

(* Just for debugging. Should be removed. *)
exception RecCheckTODO of Typedtree.expression_desc;;

let rec expression : mode -> Typedtree.expression -> Env.t =
  fun mode exp -> match exp.exp_desc with
    | Texp_ident (pth, _, _) ->
        (path mode pth)
    | Texp_let (_rec_flag, bindings, body) ->
      (* *)
      let env0 = expression mode body in
      let vars = List.fold_left (fun v b -> (pat_bound_idents b.vb_pat) @ v)
                                []
                                bindings
      in
      let env1 = Env.remove_list vars env0 in
      let env2 = list (value_binding env0 vars) mode bindings in
      Env.join env1 env2
(*
    | Texp_letmodule (x, _, m, e) ->
      let ty = modexp env m in
      Use.join (Use.discard ty) (expression (Ident.add x ty env) e)
*)
    | Texp_match (e, val_cases, exn_cases, _) ->
      (* TODO: split this fold *)
      let env_pat, m_e =
        List.fold_left
          (fun (env, m) c ->
            let (env', m') = case mode c in
            (Env.join env env'), (prec m m'))
          (Env.empty, Unused)
          val_cases
      in
      (* TODO: take exception cases into account.
       * let exn_case env {Typedtree.c_rhs} = expression env c_rhs in *)
      let env_e = expression m_e e in
      Env.join env_pat env_e
(*
    | Texp_for (_, _, e1, e2, _, e3) ->
      Use.(join
              (join
                  (inspect (expression env e1))
                  (inspect (expression env e2)))
              (* The body is evaluated, but not used, and not available
                  for inclusion in another value *)
              (discard (expression env e3)))
*)
    | Texp_constant _ ->
      Env.empty
(*
    | Texp_new (pth, _, _) ->
        Use.inspect (path env pth)
    | Texp_instvar _ ->
      Use.empty
    | Texp_apply ({exp_desc = Texp_ident (_, _, vd)}, [_, Some arg])
      when is_ref vd ->
        Use.guard (expression env arg)
*)
    | Texp_apply (e, args)  ->
        let arg m (_, eo) = option expression m eo in
        let m' = if List.exists is_abstracted_arg args
        then (* evaluate expressions, abstract over the results
                let g = f and x = e in fun z -> g ~x z *)
          failwith "TODO in apply"
          (* original code: Use.discard ty
             Should it be replaced by Delayed? *)
        else compos mode Dereferenced
        in
        Env.join (list arg m' args) (expression m' e)
    | Texp_tuple exprs ->
      list expression (compos mode Guarded) exprs
(*
    | Texp_array exprs when array_kind exp = `Pfloatarray ->
      Use.inspect (list expression env exprs)
    | Texp_array exprs when has_concrete_element_type exp ->
      Use.guard (list expression env exprs)
    | Texp_array exprs ->
      (* This is counted as a use, because constructing a generic array
          involves inspecting the elements (PR#6939). *)
      Use.inspect (list expression env exprs)
*)
    | Texp_construct (_, desc, exprs) ->
      let access_constructor =
        match desc.cstr_tag with
        | Cstr_extension (pth, _) -> failwith "TODO construct extension"
          (* Use.inspect (path env pth) *)
        | _ -> Env.empty
      in
      let m' = match desc.cstr_tag with
        | Cstr_unboxed -> failwith "TODO constructor unboxed"
          (* Original code: (fun x -> x)
             I guess it should be replaced by `mode`. *)
        | Cstr_constant _ | Cstr_block _ | Cstr_extension _ ->
          compos mode Guarded
      in
      Env.join access_constructor (list expression m' exprs)
(*
    | Texp_variant (_, eo) ->
      Use.guard (option expression env eo)
    | Texp_record { fields = es; extended_expression = eo;
                    representation = rep } ->
        let use = match rep with
          | Record_float -> Use.inspect
          | Record_unboxed _ -> (fun x -> x)
          | Record_regular | Record_inlined _
          | Record_extension -> Use.guard
        in
        let field env = function
            _, Kept _ -> Use.empty
          | _, Overridden (_, e) -> expression env e
        in
        Use.join
          (use (array field env es))
          (option expression env eo)
    | Texp_ifthenelse (cond, ifso, ifnot) ->
        Use.(join (inspect (expression env cond))
                (join
                    (expression env ifso)
                    (option expression env ifnot)))
    | Texp_setfield (e1, _, _, e2) ->
        Use.(join (inspect (expression env e1))
              (inspect (expression env e2)))
    | Texp_sequence (e1, e2) ->
      Use.(join (discard (expression env e1))
              (expression env e2))
    | Texp_while (e1, e2) ->
      Use.(join (inspect (expression env e1))
              (discard (expression env e2)))
    | Texp_send (e1, _, eo) ->
      Use.(join (inspect (expression env e1))
              (inspect (option expression env eo)))
    | Texp_field (e, _, _) ->
      Use.(inspect (expression env e))
    | Texp_setinstvar (_,_,_,e) ->
        Use.(inspect (expression env e))
    | Texp_letexception (_, e) ->
        expression env e
    | Texp_assert e ->
        Use.inspect (expression env e)
    | Texp_pack m ->
        modexp env m
    | Texp_object (clsstrct, _) ->
        class_structure env clsstrct
    | Texp_try (e, cases) ->
      (* This is more permissive than the old check. *)
      let case env {Typedtree.c_rhs} = expression env c_rhs in
      Use.join (expression env e)
        (list case env cases)
    | Texp_override (_, fields) ->
      let field env (_, _, e) = expression env e in
      Use.inspect (list field env fields)
*)
    | Texp_function { cases } ->
      (* Approximation: function `p1 -> e1, ..., pn -> en` is the same as
         `fun x -> match x with p1 -> e1, ..., pn -> en`.

         The typing of this expression is nearly the same as the typing of
         a `match` expression, the differences are:
         - e1, ..., en are evaluated in the m[Delayed] mode instead of m
         - we don't care about the mode returned by the `case` function.
         - there are no exception cases. *)
      let m = compos mode Delayed in
      list (fun m c -> fst (case m c)) m cases

    | Texp_lazy e -> failwith "TODO lazy"
(*
        begin match Typeopt.classify_lazy_argument e with
        | `Constant_or_function
        | `Identifier _
        | `Float_that_cannot_be_shortcut ->
          expression env e
        | `Other ->
          Use.delay (expression env e)
        end
*)
    | Texp_unreachable -> failwith "TODO unreachable"
    (*
      Use.empty
      *)
    | Texp_extension_constructor _ -> failwith "TODO extension_constructor"
    (*
      Use.empty
      *)
    | e -> print_string "TODO"; raise(RecCheckTODO e)

(* option f m o:
   If o is Some(x), returns f m x.
   If o is None, returns Env.empty *)
and option : 'a. (mode -> 'a -> Env.t) -> mode -> 'a option -> Env.t =
  fun f m -> Misc.Stdlib.Option.value_default (f m) ~default:Env.empty

(* list f m l:
   Compute the environments e_i = f l_i m, with l_i an element
   of the list l.
   Join the environments e_i and return the result.
*)
and list : 'a. (mode -> 'a -> Env.t) -> mode -> 'a list -> Env.t =
  fun f m ->
    List.fold_left (fun env item -> Env.join (f m item) env) Env.empty
(*
and array : 'a. (Env.env -> 'a -> Use.t) -> Env.env -> 'a array -> Use.t =
  fun f env ->
    Array.fold_left (fun typ item -> Use.join (f env item) typ) Use.empty
and class_structure : Env.env -> Typedtree.class_structure -> Use.t =
  fun env cs -> Use.(inspect (list class_field env cs.cstr_fields))
and class_field : Env.env -> Typedtree.class_field -> Use.t =
  fun env cf -> match cf.cf_desc with
    | Tcf_inherit (_, ce, _super, _inh_vars, _inh_meths) ->
        Use.inspect (class_expr env ce)
    | Tcf_val (_lab, _mut, _, cfk, _) ->
        class_field_kind env cfk
    | Tcf_method (_, _, cfk) ->
        class_field_kind env cfk
    | Tcf_constraint _ ->
        Use.empty
    | Tcf_initializer e ->
        Use.inspect (expression env e)
    | Tcf_attribute _ ->
        Use.empty
and class_field_kind : Env.env -> Typedtree.class_field_kind -> Use.t =
  fun env cfk -> match cfk with
    | Tcfk_virtual _ ->
        Use.empty
    | Tcfk_concrete (_, e) ->
        Use.inspect (expression env e)
and modexp : Env.env -> Typedtree.module_expr -> Use.t =
  fun env m -> match m.mod_desc with
    | Tmod_ident (pth, _) ->
        (path env pth)
    | Tmod_structure s ->
        structure env s
    | Tmod_functor (_, _, _, e) ->
      Use.delay (modexp env e)
    | Tmod_apply (f, p, _) ->
      Use.(join
              (inspect (modexp env f))
              (inspect (modexp env p)))
    | Tmod_constraint (m, _, _, Tcoerce_none) ->
      modexp env m
    | Tmod_constraint (m, _, _, _) ->
      Use.inspect (modexp env m)
    | Tmod_unpack (e, _) ->
        expression env e
*)
and path : mode -> Path.t -> Env.t =
  fun mode pth -> match pth with
    | Path.Pident x ->
        Env.single x mode
    |_ -> failwith "TODO"
        (*
    | Path.Pdot (t, _, _) ->
        Use.inspect (path env t)
    | Path.Papply (f, p) ->
        Use.(inspect (join (path env f) (path env p)))
        *)
(*
and structure : Env.env -> Typedtree.structure -> Use.t =
  fun env s ->
    let _, ty =
      List.fold_left
        (fun (env, ty) item ->
            let env', ty' = structure_item env item in
            Env.join env env', Use.join ty ty')
        (env, Use.empty)
        s.str_items
    in
    Use.guard ty
and structure_item : Env.env -> Typedtree.structure_item -> Env.env * Use.t =
  fun env s -> match s.str_desc with
    | Tstr_eval (e, _) ->
        Env.empty, expression env e
    | Tstr_value (rec_flag, valbinds) ->
        value_bindings rec_flag env valbinds
    | Tstr_module {mb_id; mb_expr} ->
        let ty = modexp env mb_expr in
        Ident.add mb_id ty Env.empty, ty
    | Tstr_recmodule mbs ->
        let modbind env {mb_expr} = modexp env mb_expr in
        (* Over-approximate: treat any access as a use *)
        Env.empty, Use.inspect (list modbind env mbs)
    | Tstr_primitive _ ->
        Env.empty, Use.empty
    | Tstr_type _ ->
        Env.empty, Use.empty
    | Tstr_typext _ ->
        Env.empty, Use.empty
    | Tstr_exception _ ->
        Env.empty, Use.empty
    | Tstr_modtype _ ->
        Env.empty, Use.empty
    | Tstr_open _ ->
        Env.empty, Use.empty
    | Tstr_class classes ->
        (* Any occurrence in a class definition is counted as a use,
            so there's no need to add anything to the environment. *)
        let cls env ({ci_expr=ce}, _) = class_expr env ce in
        Env.empty, Use.inspect (list cls env classes)
    | Tstr_class_type _ ->
        Env.empty, Use.empty
    | Tstr_include inc ->
        (* This is a kind of projection.  There's no need to add
            anything to the environment because everything is used in
            the type component already *)
        Env.empty, Use.inspect (modexp env inc.incl_mod)
    | Tstr_attribute _ ->
        Env.empty, Use.empty
and class_expr : Env.env -> Typedtree.class_expr -> Use.t =
  fun env ce -> match ce.cl_desc with
    | Tcl_ident (pth, _, _) ->
        Use.inspect (path env pth)
    | Tcl_structure cs ->
        class_structure env cs
    | Tcl_fun (_, _, args, ce, _) ->
        let arg env (_, e) = expression env e in
        Use.inspect (Use.join (list arg env args)
                        (class_expr env ce))
    | Tcl_apply (ce, args) ->
        let arg env (_, eo) = option expression env eo in
        Use.inspect (Use.join (class_expr env ce)
                        (list arg env args))
    | Tcl_let (rec_flag, valbinds, _, ce) ->
        let _, ty = value_bindings rec_flag env valbinds in
        Use.(inspect (join ty (class_expr env ce)))
    | Tcl_constraint (ce, _, _, _, _) ->
        class_expr env ce
    | Tcl_open (_, _, _, _, ce) ->
        class_expr env ce
*)
and case : mode -> Typedtree.case (* -> scrutinee:Use.t *) -> Env.t * mode =
  fun m { Typedtree.c_lhs; c_guard; c_rhs } (* ~scrutinee:ty *) ->
    (* TODO: take c_guard into account *)
    let env = expression m c_rhs in
    let m' = match is_destructuring_pattern c_lhs with
      | NonDestructuring(None) -> let_in Unused m
      | NonDestructuring(Some id) -> let_in (Env.find env id) m
      | Destructuring -> compos m Dereferenced
    in
    let vars = pat_bound_idents c_lhs in
    (Env.remove_list vars env), m'
(*
and value_bindings :
  rec_flag -> Env.env -> Typedtree.value_binding list -> Env.env * Use.t =
  fun rec_flag env bindings ->
    match rec_flag with
    | Recursive ->
        (* Approximation:
              let rec y =
                let rec x1 = e1
                    and x2 = e2
                  in e
            treated as
              let rec y =
                  let rec x = (e1, e2)[x1:=fst x, x2:=snd x] in
                    e[x1:=fst x, x2:=snd x]
            Further, use the fact that x1,x2 cannot occur unguarded in e1, e2
            to avoid recursive trickiness.
        *)
        let ids, ty =
          List.fold_left
            (fun (pats, tys) {vb_pat=p; vb_expr=e} ->
                (pat_bound_idents p @ pats,
                Use.join (expression env e) tys))
            ([], Use.empty)
            bindings
        in
        (List.fold_left (fun  (env : Env.env) (id : Ident.t) ->
              Ident.add id ty env) Env.empty ids,
          ty)
    | Nonrecursive ->
        List.fold_left
          (fun (env2, ty) binding ->
              let env', ty' = value_binding env binding in
              (Env.join env2 env', Use.join ty ty'))
          (Env.empty, Use.empty)
          bindings
*)
(* value_bindig env vars m bind:
   Get the environment in which this binding must be evaluated.

   The pattern and the parameter `env` are used to determine the mode in
   which the expression must be evaluated.

   `vars` is a list of indentifiers that must be removed from the resulting
   environment. *)
and value_binding : Env.t -> Ident.t list -> mode -> Typedtree.value_binding
                          -> Env.t =
  fun env vars m { vb_pat; vb_expr } ->
    let m' = match is_destructuring_pattern vb_pat with
      | NonDestructuring(None) -> let_in Unused m
      | NonDestructuring(Some id) -> let_in (Env.find env id) m
      | Destructuring -> compos m Dereferenced
    in
    let env' = expression m' vb_expr in
    Env.remove_list vars env'

and is_destructuring_pattern : Typedtree.pattern -> pattern_info =
  fun pat -> match pat.pat_desc with
    | Tpat_any -> NonDestructuring(None)
    | Tpat_var (id, _) -> NonDestructuring(Some id)
    | Tpat_alias (pat, _, _) -> failwith "TODO"
      (* is_destructuring_pattern pat *)
    | Tpat_constant _ -> Destructuring
    | Tpat_tuple _ -> Destructuring
    | Tpat_construct (_, _, _) -> Destructuring
    | Tpat_variant _ -> Destructuring
    | Tpat_record (_, _) -> Destructuring
    | Tpat_array _ -> Destructuring
    | Tpat_or (l,r,_) ->
        failwith "TODO"
        (* is_destructuring_pattern l || is_destructuring_pattern r *)
    | Tpat_lazy _ -> Destructuring

let is_valid_recursive_expression (*idlist*) _ expr =
  let ty = expression Unguarded expr in
  match Env.unguarded ty, Env.dependent ty, classify_expression expr with
  | _ :: _, _, _ (* The expression inspects rec-bound variables *)
  | _, _ :: _, Dynamic -> (* The expression depends on rec-bound variables
                              and its size is unknown *)
      false
  | [], _, Static (* The expression has known size *)
  | [], [], Dynamic -> (* The expression has unknown size,
                          but does not depend on rec-bound variables *)
      true

let is_valid_class_expr idlist ce = true
  (* let rec class_expr : Env.env -> Typedtree.class_expr -> Use.t =
    fun env ce -> match ce.cl_desc with
      | Tcl_ident (_, _, _) -> Use.empty
      | Tcl_structure _ -> Use.empty
      | Tcl_fun (_, _, _, _, _) -> Use.empty
      | Tcl_apply (_, _) -> Use.empty
      | Tcl_let (rec_flag, valbinds, _, ce) ->
          let _, ty = value_bindings rec_flag env valbinds in
          Use.join ty (class_expr env ce)
      | Tcl_constraint (ce, _, _, _, _) ->
          class_expr env ce
      | Tcl_open (_, _, _, _, ce) ->
          class_expr env ce
  in
  match Use.unguarded (class_expr (build_unguarded_env idlist) ce) with
  | [] -> true
  | _ :: _ -> false *)
