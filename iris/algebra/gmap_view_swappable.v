From iris.algebra Require Import auth gmap_view auth_swappable swappable.

(** Agreement-valued views factor into an authoritative agreement map and
    a map of discardable fractions. The strengthened relation makes validity
    exactly the conjunction of validity of those projections. We repair the
    first with [swappable_auth_core_id], keep the discrete fraction map, and
    reconstruct the original fragment domain. No choice principle is needed. *)
Section agreement_view.
  Context `{Countable K} (A : ofe).
  Local Notation V := (agreeR A).
  Local Notation M := (gmapUR K V).
  Local Notation G := (gmap_viewR K V).

  Definition gmap_view_auth_projection (x : G) : authR M :=
    View (view_auth_proj x) (snd <$> view_frag_proj x).
  Definition gmap_view_fraction_projection (x : G) : gmapUR K dfracR :=
    fst <$> view_frag_proj x.

  Lemma gmap_view_relation_projection n m f :
    gmap_view.gmap_view_rel_raw K V n m f ↔
    ✓{n} (fst <$> f : gmapUR K dfracR) ∧
    auth_view_rel_raw n m (snd <$> f : M).
  Proof.
    split.
    - intros [Hm Hr]. split.
      + intros k. rewrite lookup_fmap. destruct (f !! k) as [[dq v]|] eqn:Hk; rewrite ?Hk /=; [|done].
        destruct (Hr _ _ Hk) as [v' [dq' [Hmv [Hvalid Hinc]]]].
        eapply (cmra_validN_Some_includedN n dq'); [exact (proj1 Hvalid)|].
        eapply Some_pair_includedN_l. exact Hinc.
      + split; [|done]. apply lookup_includedN => k. rewrite lookup_fmap.
        destruct (f !! k) as [[dq v]|] eqn:Hk; rewrite ?Hk /=.
        2:{ exists (m !! k). by rewrite left_id. }
        destruct (Hr _ _ Hk) as [v' [dq' [Hmv [Hvalid Hinc]]]].
        rewrite Hmv. by apply Some_pair_includedN_r in Hinc.
    - intros [Hfrac [Hinc Hm]]. split; [done|]. intros k [dq v] Hk.
      have Hinc' := proj1 (lookup_includedN n (snd <$> f : M) m) Hinc k.
      rewrite lookup_fmap Hk /= in Hinc'.
      destruct (Some_includedN_is_Some _ _ _ Hinc') as [v' Hmv].
      rewrite Hmv in Hinc'.
      have Hv' : ✓{n} v' by move: (Hm k); rewrite Hmv.
      have Heq : v ≡{n}≡ v'.
      { apply agree_valid_includedN; [done|]. exact (proj1 (Some_includedN_total n v v') Hinc'). }
      exists v', dq. split; [done|]. split.
      + split; [move: (Hfrac k); by rewrite lookup_fmap Hk|done].
      + rewrite Heq. reflexivity.
  Qed.

  Lemma gmap_view_valid_projection n x :
    ✓{n} x ↔ ✓{n} gmap_view_auth_projection x ∧ ✓{n} gmap_view_fraction_projection x.
  Proof.
    destruct x as [a f].
    rewrite /gmap_view_auth_projection /gmap_view_fraction_projection
      !view.view_validN_eq /=.
    destruct a as [[dq ag]|]; setoid_rewrite gmap_view_relation_projection;
      naive_solver.
  Qed.

  Lemma gmap_view_auth_projection_op x y :
    gmap_view_auth_projection (x ⋅ y) ≡
    gmap_view_auth_projection x ⋅ gmap_view_auth_projection y.
  Proof.
    split; [done|]. intros k.
    rewrite /gmap_view_auth_projection /= !lookup_fmap !lookup_op !lookup_fmap.
    destruct (view_frag_proj x !! k) as [[??]|] eqn:Hx,
      (view_frag_proj y !! k) as [[??]|] eqn:Hy; rewrite ?Hx ?Hy /=; done.
  Qed.
  Lemma gmap_view_fraction_projection_op x y :
    gmap_view_fraction_projection (x ⋅ y) ≡
    gmap_view_fraction_projection x ⋅ gmap_view_fraction_projection y.
  Proof.
    intros k. rewrite /gmap_view_fraction_projection /= !lookup_fmap !lookup_op !lookup_fmap.
    destruct (view_frag_proj x !! k) as [[??]|] eqn:Hx,
      (view_frag_proj y !! k) as [[??]|] eqn:Hy; rewrite ?Hx ?Hy /=; done.
  Qed.

  (** A finite-index distance preserves presence/absence of map entries.
      The specification below therefore proves that [map_imap] drops no key,
      recovers the entire repaired value projection, and retains fractions. *)
  Definition gmap_view_rebuild (z : G) (z' : authR M) : G :=
    View (view_auth_proj z')
      (map_imap (λ k dv, (pair dv.1) <$> (view_frag_proj z' !! k)) (view_frag_proj z)).

  Lemma gmap_view_rebuild_spec n z z' :
    gmap_view_auth_projection z ≡{n}≡ z' →
    gmap_view_auth_projection (gmap_view_rebuild z z') ≡ z' ∧
    gmap_view_fraction_projection (gmap_view_rebuild z z') = gmap_view_fraction_projection z ∧
    z ≡{n}≡ gmap_view_rebuild z z'.
  Proof.
    destruct z as [za f], z' as [za' f']. intros [Ha Hf].
    split.
    - split; [done|]. intros k.
      move: (Hf k). rewrite /gmap_view_auth_projection /gmap_view_rebuild /= !lookup_fmap map_lookup_imap.
      destruct (f !! k) as [[dq v]|] eqn:Hk, (f' !! k) as [v'|] eqn:Hk';
          rewrite ?Hk ?Hk' /=; intros Heq;
        by inversion Heq.
    - split.
      + rewrite /gmap_view_fraction_projection /gmap_view_rebuild /=. apply (map_eq (M:=gmap K)) => k.
        move: (Hf k). rewrite /gmap_view_auth_projection /gmap_view_fraction_projection /gmap_view_rebuild /=
          !lookup_fmap map_lookup_imap.
        destruct (f !! k) as [[dq v]|] eqn:Hk, (f' !! k) as [v'|] eqn:Hk';
          rewrite ?Hk ?Hk' /=; intros Heq;
          by inversion Heq.
      + split; [exact Ha|]. intros k.
        move: (Hf k). rewrite /gmap_view_auth_projection /gmap_view_rebuild /= lookup_fmap map_lookup_imap.
        destruct (f !! k) as [[dq v]|] eqn:Hk, (f' !! k) as [v'|] eqn:Hk';
          rewrite ?Hk ?Hk' /=; intros Heq;
          try by inversion Heq.
        constructor. split; [done|]. by apply (inj Some) in Heq.
  Qed.

  Global Instance swappable_gmap_view_agree : CmraSwappable G.
  Proof.
    apply swappable_ucmra => n x z Hx Hz.
    have Hx' := proj1 (gmap_view_valid_projection (S n) x) Hx.
    have Hz' := proj1 (gmap_view_valid_projection n (z ⋅ x)) Hz.
    have Hauth : ✓{n} (gmap_view_auth_projection z ⋅ gmap_view_auth_projection x).
    { rewrite -gmap_view_auth_projection_op. exact (proj1 Hz'). }
    destruct (cmra_extend_included n (Some (gmap_view_auth_projection x))
      (gmap_view_auth_projection z) (proj1 Hx') Hauth) as [z' [Hv Heq]].
    destruct (gmap_view_rebuild_spec n z z' Heq) as [Hproj [Hfrac Hdist]].
    exists (gmap_view_rebuild z z'). split; [|done].
    apply (proj2 (gmap_view_valid_projection (S n) _)). split.
    - rewrite gmap_view_auth_projection_op Hproj. exact Hv.
    - rewrite gmap_view_fraction_projection_op Hfrac -gmap_view_fraction_projection_op.
      apply (proj1 (cmra_discrete_valid_iff_0 (S n) _)).
      apply (proj2 (cmra_discrete_valid_iff_0 n _)). exact (proj2 Hz').
  Qed.
End agreement_view.
