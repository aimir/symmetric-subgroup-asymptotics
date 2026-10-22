import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCharTwoQuantitative
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation

/-! Inner/outer cancellation with the literal automorphism-subgroup index
retained. This is useful for the natural-point stabilizer of D4: its index
is three even though it may interchange the two maximal-space types.
The supplied subgroup count is still a premise of this counting lemma;
the actual geometric reconstruction must establish that count. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSubgroupOuterCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open PrimitiveSocleRawStructure
variable (K : Type) [Field K] [Finite K] (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s+4))]

private theorem projective_not_commutative :
    ¬ IsMulCommutative (elementaryProjective K (s+4)) := by
  intro h
  have ht := Subgroup.center_eq_top_iff.mpr h
  have hb := elementaryProjective_center_eq_bot K s
  exact bot_ne_top (hb.symm.trans ht)

theorem outer_card_le_eight_index_field
    (H : Subgroup (MulAut (elementaryProjective K (s+4))))
    (k : ℕ) (hk : H.index ≤ k)
    (hH : Nat.card H ≤ Nat.card (quadraticPreserving K (s+4)) * Nat.card (K ≃+* K)) :
    Nat.card (Outer (elementaryProjective K (s+4))) ≤
      (8*k) * Nat.card (K ≃+* K) := by
  let E := elementaryRootGroup K (s+4)
  let G := elementaryProjective K (s+4)
  let Z := Subgroup.center E
  letI : Finite G := Finite.of_surjective (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hZ : Nat.card Z ≤ 2 := CFSGOrthogonalDCenterCardinality.center_card_le_two K s
  have hcard := Z.card_mul_index
  change Nat.card Z * Nat.card G = Nat.card E at hcard
  have hE : Nat.card E ≤ 2 * Nat.card G :=
    hcard.symm.trans_le (Nat.mul_le_mul_right _ hZ)
  have hO : Nat.card (quadraticPreserving K (s+4)) ≤ 8 * Nat.card G := by
    calc
      _ ≤ 4 * Nat.card E :=
        CFSGOrthogonalDIsometryIndexCardinality.quadratic_card_le_four_mul_elementary K s
      _ ≤ 4 * (2 * Nat.card G) := Nat.mul_le_mul_left _ hE
      _ = 8 * Nat.card G := by omega
  have hAut : Nat.card (MulAut G) ≤ Nat.card G * ((8*k) * Nat.card (K ≃+* K)) := by
    calc
      _ = H.index * Nat.card H := by rw [mul_comm]; exact H.card_mul_index.symm
      _ ≤ k * (Nat.card (quadraticPreserving K (s+4)) * Nat.card (K ≃+* K)) :=
        Nat.mul_le_mul hk hH
      _ ≤ k * ((8 * Nat.card G) * Nat.card (K ≃+* K)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hO)
      _ = Nat.card G * ((8*k) * Nat.card (K ≃+* K)) := by ac_rfl
  exact CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound
    (projective_not_commutative K s) _ hAut

theorem outer_card_le_two_index_field [CharP K 2]
    (H : Subgroup (MulAut (elementaryProjective K (s+4))))
    (k : ℕ) (hk : H.index ≤ k)
    (hH : Nat.card H ≤ Nat.card (quadraticPreserving K (s+4)) * Nat.card (K ≃+* K)) :
    Nat.card (Outer (elementaryProjective K (s+4))) ≤
      (2*k) * Nat.card (K ≃+* K) := by
  let E := elementaryRootGroup K (s+4)
  let G := elementaryProjective K (s+4)
  let Z := Subgroup.center E
  letI : Finite G := Finite.of_surjective (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hO : Nat.card (quadraticPreserving K (s+4)) ≤ 2 * Nat.card G :=
    CFSGOrthogonalDCharTwoQuantitative.quadratic_card_le_two_mul_projective K s
  have hAut : Nat.card (MulAut G) ≤ Nat.card G * ((2*k) * Nat.card (K ≃+* K)) := by
    calc
      _ = H.index * Nat.card H := by rw [mul_comm]; exact H.card_mul_index.symm
      _ ≤ k * (Nat.card (quadraticPreserving K (s+4)) * Nat.card (K ≃+* K)) :=
        Nat.mul_le_mul hk hH
      _ ≤ k * ((2 * Nat.card G) * Nat.card (K ≃+* K)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hO)
      _ = Nat.card G * ((2*k) * Nat.card (K ≃+* K)) := by ac_rfl
  exact CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound
    (projective_not_commutative K s) _ hAut

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSubgroupOuterCardinality
