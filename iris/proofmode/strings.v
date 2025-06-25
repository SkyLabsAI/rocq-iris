From iris.prelude Require Import options.
From stdpp Require Export strings.

(** * Support for Arbitrary String types

    This file implements a thin canonical structure wrapper to allow IPM tactics
    to receive any string type that can be converted to Coq's [string] type. *)

Structure to_str := ToStr {
    to_str_ty :> Type;
    to_str_str : to_str_ty -> string
  }.
Coercion to_str_str : to_str_ty >-> string.
Global Arguments ToStr [_]%_type_scope _.
Global Arguments to_str_str {_} _.
Add Printing Constructor to_str.

(** Default instance for Coq's [string] type.  *)
Canonical Structure stringTS : to_str := ToStr (fun (s : string) => s).

(** [is_str t] succeeds if the type of [t] has a [to_str] instance.
    It cannot be used in tactics returning constrs.
    Use [is_str_constr] instead. *)
Ltac is_str t := assert_succeeds (let _ := open_constr:(to_str_str t) in idtac).

(** [is_str_constr t] returns [to_str_str t] if there exists [TS] such that [t :
    to_str_ty TS]. Otherwise it returns [t] unchanged.

    We make use of the fact that [match]es returning constrs do not introduce
    introduce backtracking points but do allow internal backtracking. *)
Ltac is_str_constr t :=
  match True with
  | _ => constr:(to_str_str t)
  | _ => t
  end.

(** [is_str_ty t] succeeds if [ty] has a [to_str] instance.
    It cannot be used in tactics returning constrs.
    Use [is_str_ty_constr] instead. *)
Ltac is_str_ty ty :=
  assert_succeeds (
      let _ := open_constr:((@to_str_str _) : (ty -> _)) in
      idtac
    ).

(** [is_str_constr t] returns [@to_str_ty TS] if there exists [TS] such that [t]
    is convertible to [to_str_ty TS]. Otherwise it returns [ty] unchanged.

    We make use of the fact that [match]es returning constrs do not introduce
    introduce backtracking points but do allow internal backtracking. *)
Local Definition is_str_ty_constr_aux {A B:Type} (H : A = B) := B.
Ltac is_str_ty_constr ty :=
  match True with
  | _ =>
    let t := open_constr:(@is_str_ty_constr_aux ty (to_str_ty _) eq_refl) in
    let t := eval lazy head beta match delta [is_str_ty_constr_aux] in t in
    t
  | _ => ty
  end.

(** A version of stdpp's [String.words] compatible with [to_str]. *)
Local Definition to_str_words_list {TS : to_str} (ls : list TS) := to_str_str <$> ls.
Ltac to_str_words s :=
  match type of s with
  | list _ => eval vm_compute in (to_str_words_list s)
  | _ => eval vm_compute in (String.words (to_str_str s))
  end.
