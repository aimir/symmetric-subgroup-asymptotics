import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveActionTables
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalChevalleyPaths
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRationalFirstActionSpan

/-! Whole original rational B source spanning. Positive source-height
induction and the genuine Chevalley exchange give actual first-action
stability. No matrix/source recognition, source simplicity, integral
saturation, or field characteristic is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRationalSpan
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreLocalNilpotence
open CFSGSerreSignedRootWeights CFSGSerreChevalleyInvolution
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalPositiveSourceProfile
variable (r : ℕ)

def span : Submodule ℚ (RationalLie (CartanMatrix.B r).transpose) :=
  Submodule.span ℚ (Set.range (fun j => (vector r j).val))

theorem generators_mem (g : CartanMatrix.Generators (Fin r)) :
    generator (CartanMatrix.B r).transpose g ∈ span r := by
  have hle : Submodule.span ℤ (Set.range (fun j => (vector r j).val)) ≤
      (span r).restrictScalars ℤ := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j, rfl⟩
  exact hle (generator_mem_span r g)

private theorem positive_source_mem (j : PositiveIndex r) :
    CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j ∈ span r := by
  cases j with
  | inr j => exact Submodule.subset_span ⟨.inr (false, j), rfl⟩
  | inl i =>
    change CFSGOrthogonalBOriginalRationalCartanTail.tail r i.val ∈ span r
    unfold CFSGOrthogonalBOriginalRationalCartanTail.tail
    apply Submodule.sum_mem
    intro a ha
    by_cases h : i.val + a < r
    · rw [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, dif_pos h]
      exact Submodule.smul_mem _ _ (generators_mem r (.H ⟨i.val + a, h⟩))
    · rw [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, dif_neg h]
      exact Submodule.zero_mem _

private theorem positive_combination_mem (a : PositiveIndex r → ℚ) :
    Fintype.linearCombination ℚ (CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r) a ∈
      span r := by
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (positive_source_mem r j)

private theorem positive_root_first (sgn : Bool) (i : Fin r) (j : RootIndex r) :
    ⁅rootVector (CartanMatrix.B r).transpose sgn i, (root r false j).val⁆ ∈ span r := by
  have ht := CFSGOrthogonalBOriginalPositiveActionTables.source_tables r
  cases sgn
  · rw [show (root r false j).val =
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r (.inr j) from rfl, ht.1]
    exact positive_combination_mem r _
  · have h := ht.2 i (.inr j) (rootHeight_pos r j)
    change ⁅rootVector (CartanMatrix.B r).transpose true i, (root r false j).val⁆ = _ at h
    rw [h]
    exact positive_combination_mem r _

private theorem map_mem (x : RationalLie (CartanMatrix.B r).transpose) (hx : x ∈ span r) :
    rationalMap (CartanMatrix.B r).transpose x ∈ span r := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rcases j with i | ⟨sgn, j⟩
    · change rationalMap (CartanMatrix.B r).transpose
        (generator (CartanMatrix.B r).transpose (.H i)) ∈ span r
      rw [rationalMap_H]
      exact Submodule.neg_mem _ (generators_mem r (.H i))
    · obtain ⟨z, hz⟩ := CFSGOrthogonalBOriginalChevalleyPaths.map_root_swap r sgn j
      have he : rationalMap (CartanMatrix.B r).transpose (root r sgn j).val =
          (z : ℚ) • (root r (!sgn) j).val := by
        simpa only [Int.cast_smul_eq_zsmul] using congrArg Subtype.val hz
      change rationalMap _ (root r sgn j).val ∈ _
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr (!sgn, j), rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

private theorem negative_root_first (sgn : Bool) (i : Fin r) (j : RootIndex r) :
    ⁅rootVector (CartanMatrix.B r).transpose sgn i, (root r true j).val⁆ ∈ span r := by
  obtain ⟨z, hz⟩ := CFSGOrthogonalBOriginalChevalleyPaths.map_root_swap r true j
  have he : rationalMap (CartanMatrix.B r).transpose (root r true j).val =
      (z : ℚ) • (root r false j).val := by
    simpa only [Int.cast_smul_eq_zsmul, Bool.not_true] using congrArg Subtype.val hz
  have hpos : ⁅rootVector (CartanMatrix.B r).transpose (!sgn) i,
      rationalMap (CartanMatrix.B r).transpose (root r true j).val⁆ ∈ span r := by
    rw [he, lie_smul]
    exact Submodule.smul_mem _ _ (positive_root_first r (!sgn) i j)
  have h := map_mem r _ hpos
  rw [LieHom.map_lie, rationalMap_root, Bool.not_not, rationalMap_involutive] at h
  exact h

private theorem cartan_first (sgn : Bool) (i b : Fin r) :
    ⁅rootVector (CartanMatrix.B r).transpose sgn i,
      generator (CartanMatrix.B r).transpose (.H b)⁆ ∈ span r := by
  cases sgn
  · rw [← lie_skew (rootVector (CartanMatrix.B r).transpose false i)
      (generator (CartanMatrix.B r).transpose (.H b))]
    have hHE : ⁅generator (CartanMatrix.B r).transpose (.H b),
        rootVector (CartanMatrix.B r).transpose false i⁆ =
        ((CartanMatrix.B r).transpose b i : ℚ) • rootVector (CartanMatrix.B r).transpose false i :=
      coroot_root (CartanMatrix.B r).transpose false b i
    rw [hHE]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (generators_mem r (.E i)))
  · rw [← lie_skew (rootVector (CartanMatrix.B r).transpose true i)
      (generator (CartanMatrix.B r).transpose (.H b))]
    change -⁅generator (CartanMatrix.B r).transpose (.H b),
      generator (CartanMatrix.B r).transpose (.F i)⁆ ∈ _
    rw [generator_HF, neg_neg]
    simpa only [Int.cast_smul_eq_zsmul] using
      (Submodule.smul_mem (span r) (((CartanMatrix.B r).transpose b i : ℤ) : ℚ)
        (generators_mem r (.F i)))

theorem first_action_mem (sgn : Bool) (i : Fin r) (j : BasisIndex r) :
    ⁅rootVector (CartanMatrix.B r).transpose sgn i, (vector r j).val⁆ ∈ span r := by
  rcases j with b | ⟨neg, j⟩
  · exact cartan_first r sgn i b
  · cases neg
    · exact positive_root_first r sgn i j
    · exact negative_root_first r sgn i j

theorem span_eq_top :
    Submodule.span ℚ (Set.range (fun j => (vector r j).val)) = ⊤ :=
  CFSGSerreFiniteRationalFirstActionSpan.span_eq_top (CartanMatrix.B r).transpose
    (fun j => (vector r j).val) (generators_mem r) (first_action_mem r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRationalSpan
