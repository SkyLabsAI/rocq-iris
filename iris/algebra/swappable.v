From iris.algebra Require Import agree gmap.
From iris.algebra Require Export stepindex_finite.

(** The constructive swap axiom from iris/iris!231. *)
Class CmraSwappable (M : cmra) := {
  cmra_extend_included : ∀ n (mx : option M) z,
    ✓{S n} mx → ✓{n} (z ⋅? mx) →
    { z' | ✓{S n} (z' ⋅? mx) ∧ z ≡{n}≡ z' }
}.

Definition agree_pick {A} (x : agree A) : { a | a ∈ agree_car x }.
Proof. destruct x as [[|a l] H]; [discriminate H|]. exists a. set_solver. Defined.

Lemma agree_pick_valid {A : ofe} n (x : agree A) :
  ✓{n} x → x ≡{n}≡ to_agree (proj1_sig (agree_pick x)).
Proof.
  destruct (agree_pick x) as [a Ha]. rewrite agree_validN_def => Hv.
  split => b /=; setoid_rewrite list_elem_of_singleton; naive_solver.
Qed.

Global Instance swappable_discrete (A : cmra) `{!CmraDiscrete A} : CmraSwappable A.
Proof.
  split => n mx z _ Hv. exists z. split; [|done].
  move: Hv. by rewrite -!cmra_discrete_valid_iff.
Qed.

Global Instance swappable_agree (A : ofe) : CmraSwappable (agreeR A).
Proof.
  split => n [x|] z /= Hx Hz.
  - exists x. split; [by rewrite agree_idemp|].
    by apply agree_op_invN in Hz.
  - exists (to_agree (proj1_sig (agree_pick z))).
    split; [done|by apply agree_pick_valid].
Qed.

Global Instance swappable_option (A : cmra) `{!CmraSwappable A} :
  CmraSwappable (optionR A).
Proof.
  split => n mmx [z|] Hx Hz.
  - destruct (cmra_extend_included n (mjoin mmx) z) as [z' [Hv Heq]].
    + by destruct mmx as [[x|]|].
    + by destruct mmx as [[x|]|].
    + exists (Some z'). split; [by destruct mmx as [[x|]|]|by constructor].
  - exists None. split; [destruct mmx; rewrite /= ?left_id; done|done].
Qed.

Lemma swappable_ucmra (M : ucmra)
  (H : ∀ n (x z : M), ✓{S n} x → ✓{n} (z ⋅ x) →
    { z' | ✓{S n} (z' ⋅ x) ∧ z ≡{n}≡ z' }) : CmraSwappable M.
Proof.
  split => n [x|] z Hx Hz; first exact (H n x z Hx Hz).
  destruct (H n ε z) as [z' [Hv Heq]]; [apply ucmra_unit_validN|by rewrite right_id|].
  exists z'. by rewrite right_id in Hv.
Qed.

Global Instance swappable_gmap `{Countable K} (A : cmra) `{!CmraSwappable A} :
  CmraSwappable (gmapR K A).
Proof.
  apply swappable_ucmra => n x z Hx Hz.
  unshelve eassert (F := λ i : K,
    cmra_extend_included n (Some (x !! i)) (z !! i) _ _).
  - exact (Hx i).
  - change (✓{n} (z !! i ⋅ x !! i)). by rewrite -lookup_op.
  - exists (map_imap (λ i _, proj1_sig (F i)) z).
    split => i; rewrite ?lookup_op map_lookup_imap /=;
      case: (z !! i) (F i) => [a|] [a' [Hv Heq]]; rewrite /= ?left_id.
    + exact Hv.
    + exact (Hx i).
    + exact Heq.
    + done.
Qed.

Global Instance swappable_prod (A B : cmra) `{!CmraSwappable A, !CmraSwappable B} :
  CmraSwappable (prodR A B).
Proof.
  split => n [[a b]|] [za zb] Hx Hz.
  - change (✓{S n} a ∧ ✓{S n} b) in Hx.
    change (✓{n} (za ⋅ a) ∧ ✓{n} (zb ⋅ b)) in Hz.
    destruct (cmra_extend_included n (Some a) za (proj1 Hx) (proj1 Hz)) as [za' [Ha Heqa]].
    destruct (cmra_extend_included n (Some b) zb (proj2 Hx) (proj2 Hz)) as [zb' [Hb Heqb]].
    exists (za', zb'). by split; split.
  - change (✓{n} za ∧ ✓{n} zb) in Hz.
    destruct (cmra_extend_included n None za I (proj1 Hz)) as [za' [Ha Heqa]].
    destruct (cmra_extend_included n None zb I (proj2 Hz)) as [zb' [Hb Heqb]].
    exists (za', zb'). by split; split.
Qed.
