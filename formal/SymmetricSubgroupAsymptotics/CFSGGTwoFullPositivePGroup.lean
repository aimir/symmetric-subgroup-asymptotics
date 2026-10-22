import SymmetricSubgroupAsymptotics.CFSGGTwoRootDirectionOrder
import SymmetricSubgroupAsymptotics.CFSGMonomialWeightedSupport

/-! All six ACTUAL Weyl-conjugate positive root groups generate a
defining-characteristic p-group in the original folded matrix model.
Only transported sparse support is used; no group-order formula, Sylow
maximality or normalizer statement is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoFullPositivePGroup
open CFSGGTwoSerreMatrices CFSGGTwoPositivePGroup CFSGGTwoPositiveDirections
open CFSGGTwoRootDirectionOrder

theorem conjugate_positive_strict (K : Type) [Field K] (j : Fin 6) (x y : Index)
    (hxy : weight x ≤ weight y) :
    ((directionWord K j : Mat K) * positive K (rootNode j) *
      (↑((directionWord K j)⁻¹) : Mat K)) x y = 0 := by
  have hs (a b : Index) (c : K) (hab : (a, b) ∈ rootEdges (rootNode j)) :
      ((directionWord K j : Mat K) * Matrix.single a b c *
        (↑((directionWord K j)⁻¹) : Mat K)) x y = 0 :=
    CFSGMonomialWeightedSupport.conjugation_single_zero weight
      (directionWord K j) (directionPermutation j) (directionWeight K j)
      (directionWord_monomial K j) (directionWeight_ne_zero K j)
      a b c (edge_order j a b hab) x y hxy
  by_cases hi : rootNode j = 0
  · rw [hi, positive_zero_explicit]
    simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.add_apply, Matrix.sub_apply]
    rw [hs (pos 0) (pos 1) 1 (by simp [rootEdges, hi]),
      hs (neg 1) (neg 0) 1 (by simp [rootEdges, hi]),
      hs (pos 2) (pos 3) 1 (by simp [rootEdges, hi]),
      hs (neg 3) (neg 2) 1 (by simp [rootEdges, hi]),
      hs (pos 2) (neg 3) 1 (by simp [rootEdges, hi]),
      hs (pos 3) (neg 2) 1 (by simp [rootEdges, hi])]
    ring
  · have hi1 : rootNode j = 1 := Fin.eq_one_of_ne_zero _ hi
    rw [hi1, positive_one_explicit]
    simp only [mul_sub, sub_mul, Matrix.sub_apply]
    rw [hs (pos 1) (pos 2) 1 (by simp [rootEdges, hi1]),
      hs (neg 2) (neg 1) 1 (by simp [rootEdges, hi1])]
    ring

theorem conjugate_second_strict (K : Type) [Field K] (j : Fin 6) (x y : Index)
    (hxy : weight x ≤ weight y) :
    ((directionWord K j : Mat K) * positiveSecond K (rootNode j) *
      (↑((directionWord K j)⁻¹) : Mat K)) x y = 0 := by
  by_cases hi : rootNode j = 0
  · simp only [positiveSecond, if_pos hi]
    exact CFSGMonomialWeightedSupport.conjugation_single_zero weight
      (directionWord K j) (directionPermutation j) (directionWeight K j)
      (directionWord_monomial K j) (directionWeight_ne_zero K j)
      (pos 2) (neg 2) (-1) (second_order j hi) x y hxy
  · simp only [positiveSecond, if_neg hi, mul_zero, zero_mul, Matrix.zero_apply]

theorem positiveRoot_identity_on_nonincreasing (K : Type) [Field K] (j : Fin 6) (t : K)
    (x y : Index) (hxy : weight x ≤ weight y) :
    (positiveRoot K j t : Mat K) x y = (1 : Mat K) x y := by
  change (((directionWord K j : Mat K) *
    (1 + t • positive K (rootNode j) + t ^ 2 • positiveSecond K (rootNode j))) *
      (↑((directionWord K j)⁻¹) : Mat K)) x y = (1 : Mat K) x y
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
  rw [show (directionWord K j : Mat K) * (↑((directionWord K j)⁻¹) : Mat K) = 1 from
    (directionWord K j).val_inv]
  simp only [Matrix.add_apply, Matrix.smul_apply,
    conjugate_positive_strict K j x y hxy, conjugate_second_strict K j x y hxy,
    smul_zero, add_zero]

theorem positiveGroup_isPGroup (K : Type) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : IsPGroup p (positiveGroup K) := by
  apply CFSGWeightedRootPGroup.generated_isPGroup weight
    (fun z : Fin 6 × K => positiveRoot K z.1 z.2)
  intro z x y hxy
  exact positiveRoot_identity_on_nonincreasing K z.1 z.2 x y hxy

end SymmetricSubgroupAsymptotics.CFSGGTwoFullPositivePGroup
