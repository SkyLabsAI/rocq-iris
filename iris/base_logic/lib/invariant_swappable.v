From iris.algebra Require Import auth gmap agree gmap_view swappable
  auth_swappable gmap_view_swappable_counterexample coPset gset.
From iris.base_logic.lib Require Import iprop.
From iris.si_logic Require Import bi.
Local Arguments uPred_holds {_} !_ _ _ /.
Local Arguments siProp_holds !_ _ /.

(** The invariant resources from iris/iris!231. The original [wsat.v]
    uses later [iPreProp]; both that representation and later [iProp] are
    covered by the generic theorem. Enabled and disabled tokens are discrete.
    These are complete camera instances, not restrictions to resources that
    arise during execution of the invariant API. *)
Global Instance swappable_original_invariant (Σ : gFunctors) :
  CmraSwappable (authR (gmapUR positive (agreeR (laterO (iPropO Σ))))) := _.
Global Instance swappable_invariant_enabled : CmraSwappable coPset_disjR := _.
Global Instance swappable_invariant_disabled : CmraSwappable (gset_disjR positive) := _.

Global Instance swappable_original_invariant_preprop (Σ : gFunctors) :
  CmraSwappable (authR (gmapUR positive (agreeR (laterO (iPrePropO Σ))))) := _.
Global Instance swappable_original_invariant_resources (Σ : gFunctors) :
  CmraSwappable (prodR
    (authR (gmapUR positive (agreeR (laterO (iPrePropO Σ)))))
    (prodR coPset_disjR (gset_disjR positive))) := _.

(** Modern [wsat] uses [gmap_view] and admits an authoritative entry that
    agrees on both [Next True] and [Next False], until a fragment names it.
    This entry is valid at zero and invalid at one. Full authority for the
    singleton map is valid at one anyway. A zero-equivalent replacement for
    a singleton fragment must still mention the key, and validity at one
    would force the fixed authoritative entry to be valid at one. *)
Definition inconsistent_invariant_entry (Σ : gFunctors) : agreeR (laterO (iPropO Σ)) :=
  to_agree (Next (True%I : iProp Σ)) ⋅ to_agree (Next (False%I : iProp Σ)).

Lemma true_false_apart_at_zero (Σ : gFunctors) :
  (True%I : iProp Σ) ≡{0}≡ (False%I : iProp Σ) → False.
Proof.
  intros [H]. move: (H 0 ε (Nat.le_refl 0) (ucmra_unit_validN 0)).
  change ((uPred_holds (iris.base_logic.bi.uPred_pure (M:=iResUR Σ) True) 0 ε ↔
    uPred_holds (iris.base_logic.bi.uPred_pure (M:=iResUR Σ) False) 0 ε) → False).
  rewrite /iris.base_logic.bi.uPred_pure.
  uPred_primitive.unseal. siProp.unseal. naive_solver.
Qed.

Lemma inconsistent_invariant_entry_valid0 Σ : ✓{0} inconsistent_invariant_entry Σ.
Proof.
  rewrite /inconsistent_invariant_entry to_agree_op_validN.
  apply dist_later_0.
Qed.
Lemma inconsistent_invariant_entry_invalid1 Σ :
  ✓{1} inconsistent_invariant_entry Σ → False.
Proof.
  intros H. apply to_agree_op_invN in H.
  change (dist_later 1 (True%I : iProp Σ) (False%I : iProp Σ)) in H.
  rewrite -dist_later_S in H. exact (true_false_apart_at_zero Σ H).
Qed.

Theorem modern_invariant_not_swappable (Σ : gFunctors) :
  CmraSwappable (gmap_viewR positive (agreeR (laterO (iPropO Σ)))) → False.
Proof.
  apply (gmap_view_validity_cliff _ 0 (inconsistent_invariant_entry Σ)).
  - apply inconsistent_invariant_entry_valid0.
  - apply inconsistent_invariant_entry_invalid1.
Qed.
