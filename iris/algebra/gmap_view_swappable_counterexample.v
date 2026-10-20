From iris.algebra Require Import gmap_view swappable stepindex_finite.

(** Unlike [authR], [gmap_viewR] does not require unused authoritative
    entries to be valid. A validity cliff in the value camera therefore
    prevents swapping as soon as a new fragment mentions such an entry. *)
Theorem gmap_view_validity_cliff (V : cmra) n (bad : V) :
  ✓{n} bad → (✓{S n} bad → False) →
  CmraSwappable (gmap_viewR positive V) → False.
Proof.
  intros Hbad Hcliff Hswap.
  set (m := {[1%positive := bad]} : gmap positive V).
  set (x := gmap_view_auth (DfracOwn 1) m).
  set (z := gmap_view_frag 1%positive DfracDiscarded bad).
  have Hx : ✓{S n} x by apply gmap_view_auth_dfrac_validN.
  have Hz : ✓{n} (z ⋅ x).
  { rewrite comm /x /z gmap_view_both_dfrac_validN.
    exists bad, DfracDiscarded. split_and!; try done.
  }
  destruct (cmra_extend_included n (Some x) z Hx Hz) as [z' [Hv Hzz]].
  destruct z' as [za f].
  change (None ≡{n}≡ za ∧ {[1%positive := (DfracDiscarded, bad)]} ≡{n}≡ f) in Hzz.
  destruct Hzz as [Ha Hf].
  have Hza : za = None by apply (proj1 (dist_None n za)); symmetry.
  subst za.
  have Hlookup : Some (DfracDiscarded, bad) ≡{n}≡ f !! 1%positive.
  { move: (Hf 1%positive). by rewrite lookup_singleton_eq. }
  destruct (dist_Some_inv_l' _ _ _ Hlookup) as [[dq v] [Hfv Hdist]].
  change (✓{S n} (View (Some (DfracOwn 1, to_agree m)) (f ⋅ ε) : gmap_viewR positive V)) in Hv.
  rewrite right_id in Hv.
  change (✓{S n} (DfracOwn 1) ∧ ∃ m', to_agree m ≡{S n}≡ to_agree m' ∧
    gmap_view.gmap_view_rel_raw positive V (S n) m' f) in Hv.
  destruct Hv as [_ [m' [Hmm' Hr]]].
  apply (inj to_agree) in Hmm'.
  destruct (Hr _ _ (eq_sym Hfv)) as [v' [dq' [Hmv [Hvalid _]]]].
  have Hentry : Some bad ≡{S n}≡ Some v'.
  { move: (Hmm' 1%positive). by rewrite /m lookup_singleton_eq Hmv. }
  apply Hcliff. rewrite (proj1 (dist_Some _ _ _) Hentry).
  exact (proj2 Hvalid).
Qed.
