import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExactIntersection

/-! Equality in the integral elementary-kernel lift forces equality of
the actual mixed intersection and the prime relative radical. No higher
cyclic factor in the source or top is discarded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G H : Type} [Group G] [Finite G] [Group H] [Finite H]

theorem actual_commutator_intersection_eq_radical_of_integral_saturation
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (f : G →* H) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker,(k : G)^p=1)
    (N : Subgroup G) [N.Normal]
    (hsat : normalIntegralCoinvariantOrder N=
      p^MarkedC4.normalGen (N⊓f.ker)*normalIntegralCoinvariantOrder (N.map f)) :
    ⁅N,(⊤ : Subgroup G)⁆⊓f.ker=primeRelativeRadical p (N⊓f.ker) := by
  let A := N⊓f.ker
  let C := ⁅N,(⊤ : Subgroup G)⁆⊓f.ker
  have hle : primeRelativeRadical p A≤C := by
    rw [primeRelativeRadical_eq_powerCommutator]
    apply sup_le
    · apply (Subgroup.closure_le C).mpr
      rintro x ⟨a,rfl⟩
      change (a : G)^p∈C
      rw [hpow ⟨a.val,a.property.2⟩]
      exact C.one_mem
    · exact le_inf
        (Subgroup.commutator_mono (show A≤N from inf_le_left) le_rfl)
        ((Subgroup.commutator_le_left A ⊤).trans (show A≤f.ker from inf_le_right))
  have hcard := primeRelativeRadical_card_factorization p A
  rw [←pGroup_normalGen_eq_primeRelativeHead p hG A] at hcard
  have hexact := normalIntegralCoinvariantOrder_mul_actual_commutator_intersection f hf N
  have htop : 0<normalIntegralCoinvariantOrder (N.map f) := by
    change 0<((⁅N.map f,(⊤ : Subgroup H)⁆).subgroupOf (N.map f)).index
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hp : 0<p^MarkedC4.normalGen A :=
    Nat.pow_pos (Fact.out : p.Prime).pos
  have he : (p^MarkedC4.normalGen A*normalIntegralCoinvariantOrder (N.map f))*Nat.card C=
      (p^MarkedC4.normalGen A*normalIntegralCoinvariantOrder (N.map f))*
        Nat.card (primeRelativeRadical p A) := by
    calc
      _ = normalIntegralCoinvariantOrder N*Nat.card C := by rw [hsat]
      _ = normalIntegralCoinvariantOrder (N.map f)*Nat.card A := hexact
      _ = _ := by rw [hcard];ring
  have hc : Nat.card C=Nat.card (primeRelativeRadical p A) :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp htop) he
  exact (Subgroup.eq_of_le_of_card_ge hle hc.le).symm

/-- The equality case supplies exactly the ambient mixed-commutator
hypothesis consumed by the checked original-normal index-two engines. -/
theorem kernel_mixed_commutator_le_radical_of_integral_saturation
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (f : G →* H) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker,(k : G)^p=1)
    (N : Subgroup G) [N.Normal]
    (hsat : normalIntegralCoinvariantOrder N=
      p^MarkedC4.normalGen (N⊓f.ker)*normalIntegralCoinvariantOrder (N.map f)) :
    ⁅f.ker,N⁆≤primeRelativeRadical p (N⊓f.ker) := by
  rw [←actual_commutator_intersection_eq_radical_of_integral_saturation p hG f hf hpow N hsat]
  apply le_inf
  · rw [Subgroup.commutator_comm f.ker N]
    exact Subgroup.commutator_mono le_rfl le_top
  · exact Subgroup.commutator_le_left f.ker N
end SymmetricSubgroupAsymptotics
