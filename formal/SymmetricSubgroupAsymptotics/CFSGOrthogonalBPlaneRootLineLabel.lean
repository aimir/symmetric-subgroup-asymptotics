import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPairOperator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootLinePlaneLabel

/-! The original natural two-plane determines its whole original long
root subgroup. This is the reverse of the checked displacement-image
label and uses the literal bilinear pair operator, not a recognition
hypothesis about abstract automorphisms or polar points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGAlternatingPairOperator
variable {K : Type} [Field K] [Finite K]

private theorem conjugateRootPlane_span (s : ℕ) (g : elementaryRootGroup K (s + 3)) :
    conjugateRootPlane (K := K) s g = Submodule.span K
      {((g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s 0),
       ((g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s (secondIndex s))} := by
  change (Submodule.span K {positiveVector (K := K) s 0,
    positiveVector (K := K) s (secondIndex s)}).map (Matrix.mulVecLin (g.val : Mat K (s + 3))) = _
  rw [Submodule.map_span, Set.image_pair]
  rfl

theorem conjugate_root_element_of_plane_eq (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3))
    (hp : conjugateRootPlane (K := K) s g = conjugateRootPlane (K := K) s h) (a : K) :
    ∃ b : K, g * highestRoot s a * g⁻¹ = h * highestRoot s b * h⁻¹ := by
  have hu : (g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s 0 ∈
      conjugateRootPlane (K := K) s h := by
    rw [← hp, conjugateRootPlane_span]
    exact Submodule.subset_span (Or.inl rfl)
  have hv : (g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s (secondIndex s) ∈
      conjugateRootPlane (K := K) s h := by
    rw [← hp, conjugateRootPlane_span]
    exact Submodule.subset_span (Or.inr rfl)
  rw [conjugateRootPlane_span] at hu hv
  obtain ⟨d, hd⟩ := pairOperator_mem_span (gram K (s + 3)).toBilin'
    ((h.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s 0)
    ((h.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s (secondIndex s))
    ((g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s 0)
    ((g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s (secondIndex s)) hu hv
  refine ⟨a * d, ?_⟩
  have he : Matrix.mulVecLin (((g * highestRoot s a * g⁻¹).val : Mat K (s + 3)) - 1) =
      Matrix.mulVecLin (((h * highestRoot s (a * d) * h⁻¹).val : Mat K (s + 3)) - 1) := by
    rw [conjugate_highestRoot_displacement_pairOperator h2,
      conjugate_highestRoot_displacement_pairOperator h2, hd, smul_smul]
    have hs : (a / 2) * d = (a * d) / 2 := by ring
    rw [hs]
  have hm : (((g * highestRoot s a * g⁻¹).val : Mat K (s + 3)) - 1) =
      (((h * highestRoot s (a * d) * h⁻¹).val : Mat K (s + 3)) - 1) := by
    ext i j
    have hx := congrFun (LinearMap.congr_fun he (Pi.single j 1)) i
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hx
  apply Subtype.ext
  apply Units.ext
  have hm' := congrArg (fun M : Mat K (s + 3) => M + 1) hm
  simpa only [sub_add_cancel] using hm'

private theorem conjugateRootLine_le_of_plane_eq (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3))
    (hp : conjugateRootPlane (K := K) s g = conjugateRootPlane (K := K) s h) :
    conjugateRootLine h2 s g ≤ conjugateRootLine h2 s h := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := (mem_highestRootLine_iff h2 s y).mp hy
  obtain ⟨b, hb⟩ := conjugate_root_element_of_plane_eq h2 s g h hp a
  refine ⟨highestRoot s b, (mem_highestRootLine_iff h2 s _).mpr ⟨b, rfl⟩, ?_⟩
  change h * highestRoot s b * h⁻¹ = g * highestRoot s a * g⁻¹
  exact hb.symm

theorem conjugateRootLine_eq_iff_plane_eq (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3)) :
    conjugateRootLine h2 s g = conjugateRootLine h2 s h ↔
      conjugateRootPlane (K := K) s g = conjugateRootPlane (K := K) s h := by
  constructor
  · exact conjugateRootPlane_eq_of_rootLine_eq h2 s g h
  · intro hp
    exact le_antisymm (conjugateRootLine_le_of_plane_eq h2 s g h hp)
      (conjugateRootLine_le_of_plane_eq h2 s h g hp.symm)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
