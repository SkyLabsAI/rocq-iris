From iris.proofmode Require Import base tokens strings.
From iris.prelude Require Import options.

Inductive sel_pat :=
  | SelPure
  | SelIntuitionistic
  | SelSpatial
  | SelIdent : ident → sel_pat.

Fixpoint sel_pat_pure (ps : list sel_pat) : bool :=
  match ps with
  | [] => false
  | SelPure :: ps => true
  | _ :: ps => sel_pat_pure ps
  end.

Module sel_pat.
Fixpoint parse_go (ts : list token) (k : list sel_pat) : option (list sel_pat) :=
  match ts with
  | [] => Some (reverse k)
  | TName s :: ts => parse_go ts (SelIdent s :: k)
  | TPure None :: ts => parse_go ts (SelPure :: k)
  | TIntuitionistic :: ts => parse_go ts (SelIntuitionistic :: k)
  | TSep :: ts => parse_go ts (SelSpatial :: k)
  | _ => None
  end.
Definition parse {TS : to_str} (s : TS) : option (list sel_pat) :=
  parse_go (tokenize (to_str_str s)) [].

Ltac parse s :=
  lazymatch type of s with
  | sel_pat => constr:([s])
  | list sel_pat => s
  | ident => constr:([SelIdent s])
  | list ident => eval vm_compute in (SelIdent <$> s)
  | ?X =>
    lazymatch is_str_constr s with
    | to_str_str _ =>
      lazymatch eval vm_compute in (parse s) with
      | Some ?pats => pats
      | None => fail "sel_pat.parse: cannot parse" s "as a selection pattern"
      end
    | _ =>
      fail "sel_pat.parse: the term" s
      "is expected to be a selection pattern"
      "(usually a string),"
      "but has unexpected type" X
    end
  end.
End sel_pat.
