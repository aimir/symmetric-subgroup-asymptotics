import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalSumRootParents
import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights

/-! Exact positive-root heights, source weights, and source parent
relations in the ORIGINAL B Serre quotient. This profile does not assert
source spanning or identify source brackets from matrix images. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveSourceProfile
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreDividedPowerPaths CFSGSerreLocalNilpotence
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalRootParents
open CFSGOrthogonalBOriginalSumRootParents
variable (r : ℕ)
abbrev PositiveIndex := Fin r ⊕ RootIndex r

def source : PositiveIndex r → RationalLie (CartanMatrix.B r).transpose
  | .inl i => generator (CartanMatrix.B r).transpose (.H i)
  | .inr j => (root r false j).val

def rootHeight : RootIndex r → ℕ
  | .inl ij => ij.val.2.val - ij.val.1.val
  | .inr (.inl i) => r - i.val
  | .inr (.inr ij) => (r - ij.val.1.val) + (r - ij.val.2.val)

def height : PositiveIndex r → ℕ
  | .inl _ => 0
  | .inr j => rootHeight r j

theorem rootHeight_pos (j : RootIndex r) : 0 < rootHeight r j := by
  rcases j with ij | (i | ij)
  · have h := ij.property; simp only [rootHeight]; omega
  · have h := i.isLt; simp only [rootHeight]; omega
  · have h := ij.property
    have hi := ij.val.1.isLt
    have hj := ij.val.2.isLt
    simp only [rootHeight]
    omega

def rootWeight (a : Fin r) : RootIndex r → ℚ
  | .inl ij =>
    let start : Fin r := ⟨ij.val.2.val - 1, by have h := ij.property; omega⟩
    pathWeight (CartanMatrix.B r).transpose a start
      (steps r (descend r ij.val.1 start) 1)
  | .inr (.inl i) =>
    let last : Fin r := ⟨r - 1, by have h := i.isLt; omega⟩
    pathWeight (CartanMatrix.B r).transpose a last
      (steps r (descend r i last) 1)
  | .inr (.inr ij) =>
    let last : Fin r := ⟨r - 1, by have h := ij.val.2.isLt; omega⟩
    let previous : Fin r := ⟨r - 2, by have h := ij.property; have hj := ij.val.2.isLt; omega⟩
    pathWeight (CartanMatrix.B r).transpose a previous
      (steps r (descend r ij.val.1 previous) 1 ++ [(last, 2)] ++
        steps r (descend r ij.val.2 last) 1)

def weight (a : Fin r) : PositiveIndex r → ℚ
  | .inl _ => 0
  | .inr j => rootWeight r a j

private theorem positive_path_weight (a start : Fin r) (ss : List (Fin r × ℕ)) :
    ⁅coroot (CartanMatrix.B r).transpose false a, (path r false start ss).val⁆ =
      pathWeight (CartanMatrix.B r).transpose a start ss • (path r false start ss).val := by
  simpa only [path, Bool.false_eq_true, if_false, one_smul] using
    pathVector_weight (CartanMatrix.B r).transpose false a start ss

theorem root_weight (a : Fin r) (j : RootIndex r) :
    ⁅coroot (CartanMatrix.B r).transpose false a, (root r false j).val⁆ =
      rootWeight r a j • (root r false j).val := by
  rcases j with ij | (i | ij)
  · exact positive_path_weight r a _ _
  · exact positive_path_weight r a _ _
  · simp only [root, sumRoot, neg_one_smul, Submodule.coe_neg, lie_neg,
      rootWeight, positive_path_weight, smul_neg]

theorem source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.B r).transpose false a, source r j⁆ =
      weight r a j • source r j := by
  cases j with
  | inl i =>
    simpa only [source, weight, zero_smul, coroot, Bool.false_eq_true, if_false] using
      coroots_commute (CartanMatrix.B r).transpose false a i
  | inr j => exact root_weight r a j

/-- Every nonsimple positive root has an actual original first-action
parent, with a nonzero rational coefficient (always one or two). -/
theorem induction_parent (j : RootIndex r) (hj : 1 < rootHeight r j) :
    ∃ (i : Fin r) (p : RootIndex r) (c : ℚ), c ≠ 0 ∧
      0 < rootHeight r p ∧ rootHeight r p + 1 = rootHeight r j ∧
      ⁅rootVector (CartanMatrix.B r).transpose false i, (root r false p).val⁆ =
        c • (root r false j).val := by
  rcases j with ij | (i | ij)
  · let i := ij.val.1
    let k := ij.val.2
    have hik : i.val + 1 < k.val := by change 1 < k.val - i.val at hj; omega
    let next : Fin r := ⟨i.val + 1, by have hk := k.isLt; omega⟩
    let pair : Pair r := ⟨(next, k), hik⟩
    refine ⟨i, .inl pair, 1, by decide, ?_, ?_, ?_⟩
    · change 0 < k.val - (i.val + 1); omega
    · change k.val - (i.val + 1) + 1 = k.val - i.val; omega
    · have h := congrArg Subtype.val (positive_difference_parent r i k hik)
      simpa only [integralOperator_one_coe_apply, LieAlgebra.ad_apply,
        root, pair, next, i, k, one_smul] using h
  · have hi := i.isLt
    have hir : i.val + 1 < r := by change 1 < r - i.val at hj; omega
    let next : Fin r := ⟨i.val + 1, hir⟩
    refine ⟨i, .inr (.inl next), 1, by decide, ?_, ?_, ?_⟩
    · change 0 < r - (i.val + 1); omega
    · change r - (i.val + 1) + 1 = r - i.val; omega
    · have h := congrArg Subtype.val (positive_short_parent r i hir)
      simpa only [integralOperator_one_coe_apply, LieAlgebra.ad_apply,
        root, next, one_smul] using h
  · let i := ij.val.1
    let k := ij.val.2
    have hik : i.val < k.val := ij.property
    have hk := k.isLt
    by_cases hkr : k.val + 1 < r
    · let next : Fin r := ⟨k.val + 1, hkr⟩
      let pair : Pair r := ⟨(i, next), by dsimp [next]; omega⟩
      refine ⟨k, .inr (.inr pair), 1, by decide, ?_, ?_, ?_⟩
      · change 0 < (r - i.val) + (r - (k.val + 1)); omega
      · change (r - i.val) + (r - (k.val + 1)) + 1 = (r - i.val) + (r - k.val); omega
      · have h := congrArg Subtype.val (positive_sum_second_parent r i k hkr hik)
        simpa only [integralOperator_one_coe_apply, LieAlgebra.ad_apply,
          root, pair, next, i, k, one_smul] using h
    · have hlast : k.val + 1 = r := by omega
      by_cases hgap : i.val + 1 < k.val
      · let next : Fin r := ⟨i.val + 1, by omega⟩
        let pair : Pair r := ⟨(next, k), hgap⟩
        refine ⟨i, .inr (.inr pair), 1, by decide, ?_, ?_, ?_⟩
        · change 0 < (r - (i.val + 1)) + (r - k.val); omega
        · change (r - (i.val + 1)) + (r - k.val) + 1 = (r - i.val) + (r - k.val); omega
        · have h := congrArg Subtype.val (positive_sum_terminal_first_parent r i k hlast hgap)
          simpa only [integralOperator_one_coe_apply, LieAlgebra.ad_apply,
            root, pair, next, i, k, one_smul] using h
      · have hadj : i.val + 1 = k.val := by omega
        refine ⟨k, .inr (.inl i), 2, by decide, ?_, ?_, ?_⟩
        · change 0 < r - i.val; omega
        · change r - i.val + 1 = (r - i.val) + (r - k.val); omega
        · have h := congrArg Subtype.val (positive_adjacent_terminal_sum_parent r i k hadj hlast)
          simpa only [integralOperator_one_coe_apply, LieAlgebra.ad_apply,
            two_nsmul, two_smul, Submodule.coe_add, root, i, k] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveSourceProfile
