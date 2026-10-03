import SymmetricSubgroupAsymptotics.ActualWreathCompressionTower

/-!
# Exact local-order accounting for an actual wreath-compression tower

The coefficient estimates use the prime dimensions and simple factors which
occur along the literal local chief tower.  This file proves that their
product is exactly the order of the original local component.  Consequently
later analytic estimates may spend logarithmic budget on chief factors
without introducing a catalogue or a new group-theoretic hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Product of the literal local chief-factor orders displayed by a tower. -/
def localFactorOrderProduct :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℕ
  | _, .terminal _ _ => 1
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact C.p ^ Module.finrank (ZMod C.p) C.V *
        localFactorOrderProduct next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact (∏ i : C.ι, Nat.card (C.factor i)) *
        localFactorOrderProduct next

private theorem card_eq_ker_mul_of_surjective
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card f.ker * Nat.card H := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  exact h.trans (Nat.mul_comm _ _)

/-- The displayed chief-factor product is the exact local component order. -/
theorem localFactorOrderProduct_eq_card :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
        T.localFactorOrderProduct = Nat.card S.D
  | _, .terminal S hD => by
      letI : Subsingleton S.D := hD
      simp only [localFactorOrderProduct]
      exact (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩).symm
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hker : Nat.card phi.ker =
          C.p ^ Module.finrank (ZMod C.p) C.V := by
        calc
          Nat.card phi.ker = Nat.card C.V := Nat.card_congr C.equiv.toEquiv
          _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
            rw [Module.natCard_eq_pow_finrank (K := ZMod C.p) (V := C.V),
              Nat.card_zmod]
      rw [localFactorOrderProduct, localFactorOrderProduct_eq_card next,
        ← hker]
      exact (card_eq_ker_mul_of_surjective phi hphi).symm
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hker : Nat.card phi.ker = ∏ i : C.ι, Nat.card (C.factor i) := by
        calc
          Nat.card phi.ker = Nat.card ((i : C.ι) → C.factor i) :=
            Nat.card_congr C.equiv.toEquiv
          _ = ∏ i : C.ι, Nat.card (C.factor i) := Nat.card_pi
      rw [localFactorOrderProduct, localFactorOrderProduct_eq_card next,
        ← hker]
      exact (card_eq_ker_mul_of_surjective phi hphi).symm

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
