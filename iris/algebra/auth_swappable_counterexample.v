From iris.algebra Require Import auth swappable.

(** Counterexample to preservation of [CmraSwappable] by [authR].

    The base unital camera is zero ([None]) or a positive rational amount
    ([Some (Next q)]). Addition is ordinary rational addition. At index zero,
    all positive amounts are equivalent, but zero remains distinct. At every
    positive index, amounts must be equal. All base resources are valid, so
    swappability holds by taking [z' = z].

    Set [a = Some (Next 1)], [x = ● a ⋅ ◯ a], and [z = ◯ a].
    Then [x] is valid at index one, and [z ⋅ x] is valid at index zero.
    A resource [z'] equivalent to [z] at index zero must still have no
    authority and a strictly positive fragment. Validity of [z' ⋅ x] at
    index one would require [1 + q ≤ 1] for a positive [q], a contradiction.

    This uses full authority only. The same witness applies to the exclusive
    authoritative camera in the original 2019 merge request: its relevant
    validity law is also [✓{n} (● a ⋅ ◯ b) ↔ b ≼{n} a ∧ ✓{n} a].
    The original invariant camera is instead covered by [auth_swappable.v];
    it satisfies the additional core-idempotence hypothesis. The current
    [gmap_view] invariant camera is treated in [invariant_swappable.v]. *)

(** Positive rational addition, with amounts hidden for one step. All amounts
    are valid. There is no core; [optionUR] will add the zero resource.
    At index zero, extension splits any amount into two halves. *)
Definition delayed_frac := later Qp.
Canonical Structure delayed_fracO := laterO (leibnizO Qp).
Global Instance delayed_frac_cofe : Cofe delayed_fracO := _.
Local Instance delayed_frac_op : Op delayed_frac :=
  λ x y, Next (later_car x + later_car y)%Qp.
Local Instance delayed_frac_pcore : PCore delayed_frac := λ _, None.
Local Instance delayed_frac_valid : Valid delayed_frac := λ _, True.
Local Instance delayed_frac_validN : ValidN delayed_frac := λ _ _, True.

Lemma delayed_frac_cmra_mixin : CmraMixin delayed_frac.
Proof.
  split.
  - intros [p] n [q] [r] H. destruct n as [|n].
    + apply dist_later_0.
    + apply dist_later_S in H. apply dist_later_S.
      change (q = r) in H. by subst r.
  - intros n x y cx _ H. discriminate H.
  - intros n x y _ _. done.
  - intros x. done.
  - intros n n' x _ _. done.
  - intros [p] [q] [r]. apply Qp.add_assoc.
  - intros [p] [q]. apply Qp.add_comm.
  - intros x cx H. discriminate H.
  - intros x cx H. discriminate H.
  - intros x y cx _ H. discriminate H.
  - intros n x y _. done.
  - intros [|n] [p] [q] [r] _ H.
    + exists (Next (p/2)%Qp), (Next (p/2)%Qp).
      split; [symmetry; apply Qp.div_2|]. split; apply dist_later_0.
    + apply dist_later_S in H.
      exists (Next q), (Next r). split; [exact H|]. split; reflexivity.
Qed.
Canonical Structure delayed_fracR := Cmra delayed_frac delayed_frac_cmra_mixin.
Canonical Structure counterexampleUR := optionUR delayed_fracR.

Global Instance counterexample_swappable : CmraSwappable counterexampleUR.
Proof.
  split. intros n mx z _ _. exists z. split; [|done].
  destruct mx as [[p|]|], z as [q|]; done.
Qed.

Definition amount : counterexampleUR := Some (Next 1%Qp).
Definition fixed_resource : auth counterexampleUR := ● amount ⋅ ◯ amount.
Definition extra_resource : auth counterexampleUR := ◯ amount.

Lemma fixed_resource_valid : ✓{1} fixed_resource.
Proof. apply auth_both_validN. split; [reflexivity|done]. Qed.

Lemma extra_resource_valid_at_zero : ✓{0} (extra_resource ⋅ fixed_resource).
Proof.
  rewrite /extra_resource /fixed_resource (comm _ (◯ amount)) -assoc
    -auth_frag_op auth_both_validN.
  split; [|done]. exists None. constructor. apply dist_later_0.
Qed.

Lemma no_extra_resource_at_one (z' : auth counterexampleUR) :
  extra_resource ≡{0}≡ z' → ¬ ✓{1} (z' ⋅ fixed_resource).
Proof.
  intros Hz Hv.
  destruct z' as [za zb].
  change (None ≡{0}≡ za ∧ amount ≡{0}≡ zb) in Hz.
  destruct Hz as [Ha Hb].
  symmetry in Ha. apply dist_None in Ha. subst za.
  destruct zb as [[q]|]; last by inversion Hb.
  change (✓{1} (◯ (Some (Next q) : counterexampleUR) ⋅ fixed_resource)) in Hv.
  move: Hv.
  rewrite /fixed_resource (comm _ (◯ (Some (Next q) : counterexampleUR))) -assoc
    -auth_frag_op auth_both_validN.
  intros [Hincl _]. destruct Hincl as [c H]. destruct c as [[r]|].
  - change (Some (Next 1%Qp) ≡{1}≡ Some (Next (1 + q + r)%Qp)) in H.
    rewrite dist_Some in H.
    change (dist_later (A:=leibnizO Qp) 1 1%Qp (1 + q + r)%Qp) in H.
    rewrite -dist_later_S in H.
    change (1%Qp = (1 + q + r)%Qp) in H.
    rewrite -Qp.add_assoc in H. exact (Qp.add_id_free 1 (q+r)%Qp (eq_sym H)).
  - change (Some (Next 1%Qp) ≡{1}≡ Some (Next (1 + q)%Qp)) in H.
    rewrite dist_Some in H.
    change (dist_later (A:=leibnizO Qp) 1 1%Qp (1 + q)%Qp) in H.
    rewrite -dist_later_S in H.
    change (1%Qp = (1 + q)%Qp) in H.
    exact (Qp.add_id_free 1 q (eq_sym H)).
Qed.

Theorem auth_not_swappable : CmraSwappable (authR counterexampleUR) → False.
Proof.
  intros Hswap.
  destruct (cmra_extend_included 0 (Some fixed_resource) extra_resource)
    as [z' [Hv Hz]].
  - exact fixed_resource_valid.
  - exact extra_resource_valid_at_zero.
  - exact (no_extra_resource_at_one z' Hz Hv).
Qed.
