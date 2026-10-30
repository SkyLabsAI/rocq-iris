From iris.algebra Require Import auth swappable stepindex_finite gmap.
Set Default Proof Using "Type*".

(** Authoritative swappability does hold when every base resource is
    core-idempotent. Inclusion is then absorption: [b ≼{n} a] implies
    [a ≡{n}≡ b ⋅ a]. This lets us use constructive CMRA extension without
    extracting a witness from the propositional inclusion relation.

    The bounded case keeps the authority fixed. The unbounded case first
    uses base swappability to repair the authority around the fixed fragment.
    Fractional and discarded authorities are covered by the same proof. *)
Section core_id_auth.
  Context (A : ucmra) `{!CmraSwappable A}.
  Context (Hcore : ∀ a : A, CoreId a).
  Local Existing Instance Hcore.

  Lemma core_id_absorbN n (a b : A) : b ≼{n} a → a ≡{n}≡ b ⋅ a.
  Proof.
    intros [r Hr]. rewrite Hr assoc -(core_id_dup b). done.
  Qed.

  Lemma core_id_join_includedN n (a b c : A) :
    b ≼{n} a → c ≼{n} a → b ⋅ c ≼{n} a.
  Proof.
    intros Hb Hc. rewrite (core_id_dup a).
    by apply cmra_monoN.
  Qed.

  Lemma core_id_bounded_extend n (a c : A) :
    ✓{S n} a → c ≼{n} a →
    { c' | c ≡{n}≡ c' ∧ c' ≼ a }.
  Proof.
    intros Hva Hca.
    destruct (cmra_extend n a c a) as [c' [r [Ha [Hc _]]]].
    - by apply cmra_validN_S.
    - by apply core_id_absorbN.
    - exists c'. split; [by symmetry|by exists r].
  Qed.

  Lemma core_id_unbounded_extend n (a b c : A) :
    ✓{S n} b → ✓{n} a → b ⋅ c ≼{n} a →
    { ac' : A * A | a ≡{n}≡ ac'.1 ∧ c ≡{n}≡ ac'.2 ∧
      ✓{S n} ac'.1 ∧ b ⋅ ac'.2 ≼{S n} ac'.1 }.
  Proof.
    intros Hvb Hva Hbc.
    have Hb : b ≼{n} a by etrans; [apply cmra_includedN_l|exact Hbc].
    have Hc : c ≼{n} a by etrans; [apply cmra_includedN_r|exact Hbc].
    have Hab : a ≡{n}≡ a ⋅ b by rewrite comm; apply core_id_absorbN.
    destruct (cmra_extend_included n (Some b) a) as [a' [Hva' Haa']].
    - exact Hvb.
    - change (✓{n} (a ⋅ b)). by rewrite -Hab.
    - have Haa : a ≡{n}≡ a' ⋅ b by rewrite -Haa' -Hab.
      destruct (core_id_bounded_extend n (a' ⋅ b) c) as [c' [Hcc' Hca']].
      + exact Hva'.
      + by rewrite -Haa.
      + exists (a' ⋅ b, c'). split_and!; try done.
        apply core_id_join_includedN; [apply cmra_includedN_r|].
        by apply cmra_included_includedN.
  Qed.

  Lemma auth_raw_validN n dq (ag : agree A) b :
    ✓{n} (View (Some (dq, ag)) b : authR A) ↔
    ✓ dq ∧ ag ≡{n}≡ to_agree (proj1_sig (agree_pick ag)) ∧
    b ≼{n} proj1_sig (agree_pick ag) ∧ ✓{n} proj1_sig (agree_pick ag).
  Proof.
    change ((✓{n} dq ∧ ∃ a, ag ≡{n}≡ to_agree a ∧
      b ≼{n} a ∧ ✓{n} a) ↔
      ✓ dq ∧ ag ≡{n}≡ to_agree (proj1_sig (agree_pick ag)) ∧
      b ≼{n} proj1_sig (agree_pick ag) ∧ ✓{n} proj1_sig (agree_pick ag)).
    rewrite -cmra_discrete_valid_iff.
    split.
    - intros [Hq [a [Ha [Hb Hv]]]].
      have Hag : ✓{n} ag by rewrite Ha.
      have Hp := agree_pick_valid n ag Hag.
      have Hpa : proj1_sig (agree_pick ag) ≡{n}≡ a.
      { apply (inj to_agree). by rewrite -Hp Ha. }
      split_and!; try done; by rewrite Hpa.
    - intros [Hq [Ha [Hb Hv]]]. split; [done|].
      exists (proj1_sig (agree_pick ag)). done.
  Qed.

  Global Instance swappable_auth_core_id : CmraSwappable (authR A).
  Proof.
    apply swappable_ucmra => n [xa b] [za c] Hx Hz.
    destruct xa as [[qx ax]|], za as [[qz az]|].
    - apply auth_raw_validN in Hx. destruct Hx as [Hqx [Hax [Hb Hva]]].
      change (✓{n} (View (Some (qz ⋅ qx, az ⋅ ax)) (c ⋅ b) : authR A)) in Hz.
      apply auth_raw_validN in Hz. destruct Hz as [Hq [Hazax [Hcb Hav]]].
      have Haz : az ≡{n}≡ ax.
      { apply agree_op_invN. by rewrite Hazax. }
      have Haxn : ax ≡{n}≡ to_agree (proj1_sig (agree_pick ax)).
      { by apply dist_S. }
      have Hpick : proj1_sig (agree_pick (az ⋅ ax)) ≡{n}≡ proj1_sig (agree_pick ax).
      { apply (inj to_agree).
        trans (az ⋅ ax); [by symmetry|].
        trans (ax ⋅ ax); [by f_equiv|]. by rewrite agree_idemp. }
      have Hca : c ≼{n} proj1_sig (agree_pick ax).
      { etrans; [apply cmra_includedN_l|]. by rewrite -Hpick. }
      destruct (core_id_bounded_extend n _ c Hva Hca) as [c' [Hcc Hinc]].
      exists (View (Some (qz, to_agree (proj1_sig (agree_pick ax)))) c').
      split.
      + change (✓{S n} (View (Some (qz ⋅ qx, to_agree (proj1_sig (agree_pick ax)) ⋅ ax)) (c' ⋅ b) : authR A)).
        change (✓{S n} (qz ⋅ qx) ∧ ∃ a,
          to_agree (proj1_sig (agree_pick ax)) ⋅ ax ≡{S n}≡ to_agree a ∧
          c' ⋅ b ≼{S n} a ∧ ✓{S n} a).
        split; [by apply cmra_discrete_valid_iff|].
        exists (proj1_sig (agree_pick ax)). split; [by rewrite -Hax agree_idemp|].
        split; [|done]. apply core_id_join_includedN; [by apply cmra_included_includedN|done].
      + split; [constructor; split; [done|etrans; [exact Haz|exact Haxn]]|done].
    - apply auth_raw_validN in Hx. destruct Hx as [Hqx [Hax [Hb Hva]]].
      change (✓{n} (View (Some (qx, ax)) (c ⋅ b) : authR A)) in Hz.
      apply auth_raw_validN in Hz. destruct Hz as [_ [_ [Hcb _]]].
      have Hca : c ≼{n} proj1_sig (agree_pick ax).
      { etrans; [apply cmra_includedN_l|done]. }
      destruct (core_id_bounded_extend n _ c Hva Hca) as [c' [Hcc Hinc]].
      exists (View None c'). split.
      + change (✓{S n} (View (Some (qx, ax)) (c' ⋅ b) : authR A)).
        apply auth_raw_validN. split_and!; try done.
        apply core_id_join_includedN; [by apply cmra_included_includedN|done].
      + by split.
    - change (✓{S n} (◯ b : authR A)) in Hx. apply (proj1 (auth_frag_validN _ _)) in Hx.
      change (✓{n} (View (Some (qz, az)) (c ⋅ b) : authR A)) in Hz.
      apply auth_raw_validN in Hz. destruct Hz as [Hq [Haz [Hcb Hva]]].
      have Hbc : b ⋅ c ≼{n} proj1_sig (agree_pick az) by rewrite comm.
      destruct (core_id_unbounded_extend n _ b c Hx Hva Hbc)
        as [[a' c'] [Haa [Hcc [Hva' Hinc]]]].
      simpl in Haa, Hcc, Hva', Hinc.
      exists (View (Some (qz, to_agree a')) c'). split.
      + change (✓{S n} qz ∧ ∃ a, to_agree a' ≡{S n}≡ to_agree a ∧
          c' ⋅ b ≼{S n} a ∧ ✓{S n} a).
        split; [by apply cmra_discrete_valid_iff|].
        exists a'. split; [done|]. split; [by rewrite comm|done].
      + split; [|exact Hcc]. constructor. split; [done|].
        trans (to_agree (proj1_sig (agree_pick az))); [exact Haz|].
        by apply to_agree_ne.
    - change (✓{S n} (◯ b : authR A)) in Hx.
      apply (proj1 (auth_frag_validN _ _)) in Hx.
      change (✓{n} (◯ (c ⋅ b) : authR A)) in Hz.
      apply (proj1 (auth_frag_validN _ _)) in Hz.
      destruct (cmra_extend_included n (Some b) c Hx Hz) as [c' [Hv Hcc]].
      exists (View None c'). split; [|by split].
      change (✓{S n} (◯ (c' ⋅ b) : authR A)). by apply (proj2 (auth_frag_validN _ _)).
  Qed.
End core_id_auth.

(** The authoritative camera used by the original invariant implementation.
    No discreteness assumption is made on [A], in particular [A] may be
    [laterO (iPropO Σ)]. *)
Global Instance swappable_invariant_auth (A : ofe) :
  CmraSwappable (authR (gmapUR positive (agreeR A))).
Proof. apply swappable_auth_core_id; [apply _|intros a; apply _]. Qed.
