import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveCardLower
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality

/-! Actual lower order bounds for every original ReeF4 parameter and Tits.
Two disjoint opposed Sylows are retained in the SAME derived group and its
full central quotient; their proved injectivity also separates their images.
No whole-fixed-group perfectness or known exceptional order is invoked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterOrderLower
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourDerivedOppositeSylow
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourDerivedPositiveCardLower
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem derivedPositive_square_le_original_order (m : ℕ) :
    (Nat.card (derivedPositive m))^2 ≤ Nat.card (CFSG.Models.ReeF4 m) := by
  have hP : Nat.card (positiveSylow m) = Nat.card (derivedPositive m) :=
    Nat.card_congr (MulEquiv.subgroupCongr (positiveSylow_coe m)).toEquiv
  have hQ : Nat.card (negativeSylow m) = Nat.card (derivedPositive m) := by
    calc
      _ = Nat.card ((derivedPositive m).map (derivedOppositionAut m).toMonoidHom) :=
        Nat.card_congr (MulEquiv.subgroupCongr (negativeSylow_coe m)).toEquiv
      _ = Nat.card (derivedPositive m) :=
        (Nat.card_congr ((derivedOppositionAut m).subgroupMap (derivedPositive m)).toEquiv).symm
  have hc := CFSGDisjointSylowProjectiveCardinality.card_mul_le_central_quotient
    (positiveSylow m) (negativeSylow m) (opposite_inf m)
  rw [hP, hQ] at hc
  have he : Nat.card (CFSG.Models.ReeF4 m) =
      Nat.card (commutator (originalModelFixed m) ⧸
        Subgroup.center (commutator (originalModelFixed m))) :=
    Nat.card_congr (originalReeEquiv m).toEquiv
  simpa only [pow_two] using hc.trans_eq he.symm

theorem original_order_lower (m : ℕ) :
    (2^(2*m+1))^18 ≤ Nat.card (CFSG.Models.ReeF4 m) := by
  calc
    _ = ((2^(2*m+1))^9)^2 := by ring
    _ ≤ (Nat.card (derivedPositive m))^2 :=
      Nat.pow_le_pow_left (derivedPositive_card_lower m) 2
    _ ≤ _ := derivedPositive_square_le_original_order m

theorem tits_order_lower : 262144 ≤ Nat.card CFSG.Models.Tits := by
  have h := original_order_lower 0
  norm_num at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterOrderLower
