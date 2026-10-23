import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalQuotient
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementUnique
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard

/-! The literal middle radical is the already proved short complement.
Its exact cardinality follows from the genuine complementary outer
three-parameter subgroup and the actual twelve-root positive order.
No new root normal form or exceptional order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCardinality
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckShortComplement
open CFSGTrialityGeckShortComplementFactor CFSGTrialityGeckShortComplementUnique
open CFSGTrialityGeckOuterParameterChart CFSGTrialityGeckPositiveTwist
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

theorem middleRadical_eq_shortComplement (K : Type) [Field K] :
    middleRadical K = shortComplement K := by
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨k, hk, hkmid, a, ha⟩
    exact ⟨⟨k, hk⟩, hkmid, a, ha⟩
  · rintro ⟨k, hkmid, a, ha⟩
    exact ⟨k.val, k.property, hkmid, a, ha⟩

private theorem factor_card {G : Type*} [Group G] (H P Q : Subgroup G)
    (hP : P ≤ H) (hQ : Q ≤ H) (hPQ : P ⊓ Q = ⊥)
    (hfactor : ∀ x ∈ H, ∃ p ∈ P, ∃ q ∈ Q, x = p*q) :
    Nat.card P * Nat.card Q = Nat.card H := by
  let f : P × Q → H := fun z => ⟨z.1.val*z.2.val, H.mul_mem (hP z.1.property) (hQ z.2.property)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    exact CFSGDisjointSubgroupProductCard.product_injective P Q hPQ (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hPelt, q, hQelt, he⟩ := hfactor x hx
    exact ⟨(⟨p, hPelt⟩, ⟨q, hQelt⟩), Subtype.ext he.symm⟩
  simpa only [Nat.card_prod] using Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem outerGroup_card (K : Type) [Field K] : Nat.card (outerGroup K) = Nat.card K ^ 3 := by
  calc
    Nat.card (outerGroup K) = Nat.card (Fin 3 → Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective (outerProductHom_injective K)).toEquiv).symm
    _ = Nat.card K ^ 3 := by
      rw [Nat.card_fun, Nat.card_fin, Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)]

theorem middleRadical_card (K : Type) [Field K] [Finite K] :
    Nat.card (middleRadical K) = Nat.card K ^ 9 := by
  have hfactor := factor_card (Positive K) (shortComplement K) (outerGroup K)
    (shortComplement_le_positive K) (outerGroup_le_positive K) (shortComplement_inf_outer K) (by
      intro x hx
      obtain ⟨c, hc, a, he⟩ := positive_short_factor K x hx
      exact ⟨c, hc, outerProductHom K a, ⟨a, rfl⟩, he⟩)
  rw [outerGroup_card] at hfactor
  have hpositive : Nat.card (Positive K) = Nat.card K ^ 12 := by
    have h := CFSGNormTwoCoordinatePositiveCardinality.positive_card A hd hs hp ho K
    change Nat.card (Positive K) = Nat.card K ^
      Nat.card CFSGTrialityD4PositiveRootIndex.Positive at h
    simpa only [CFSGTrialityD4PositiveRootIndex.positive_card] using h
  rw [hpositive] at hfactor
  rw [middleRadical_eq_shortComplement]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := K)) 3)
  calc
    Nat.card K ^ 3 * Nat.card (shortComplement K) = Nat.card K ^ 12 := by
      simpa only [mul_comm] using hfactor
    _ = Nat.card K ^ 3 * Nat.card K ^ 9 := by rw [← pow_add]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCardinality
