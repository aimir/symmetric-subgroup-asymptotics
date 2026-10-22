import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairOperator

/-! A natural two-plane determines the whole actual conjugate D
highest-root subgroup. This is a direct same-coordinate statement in
the original elementary group, valid also in characteristic two. It
does not assert an abstract automorphism/geometry classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexHighestRoot CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPairOperator
open CFSGAlternatingPairOperator
variable (K : Type) [Field K]

def highestRootLine (s : ℕ) : Subgroup (elementaryRootGroup K (s + 4)) :=
  (Subgroup.center (unipotent K (s + 4))).map (unipotent K (s + 4)).subtype

theorem mem_highestRootLine_iff (s : ℕ) (x : elementaryRootGroup K (s + 4)) :
    x ∈ highestRootLine K s ↔ ∃ a : K, x = highestRoot K s a := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := center_eq_highestInU K s u hu
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨highestInU K s a, highestInU_mem_center K s a, rfl⟩

def conjugateRootLine (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    Subgroup (elementaryRootGroup K (s + 4)) :=
  (highestRootLine K s).map (MulAut.conj g).toMonoidHom

def conjugateRootPlane (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    Submodule K (Index (s + 4) → K) :=
  Submodule.span K {((g.val : Mat K (s + 4)) *ᵥ firstVector K s),
    ((g.val : Mat K (s + 4)) *ᵥ secondVector K s)}

theorem conjugate_root_element_of_plane_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hp : conjugateRootPlane K s g = conjugateRootPlane K s h) (a : K) :
    ∃ b : K, g * highestRoot K s a * g⁻¹ = h * highestRoot K s b * h⁻¹ := by
  have hu : (g.val : Mat K (s + 4)) *ᵥ firstVector K s ∈ conjugateRootPlane K s h := by
    rw [← hp]
    exact Submodule.subset_span (Or.inl rfl)
  have hv : (g.val : Mat K (s + 4)) *ᵥ secondVector K s ∈ conjugateRootPlane K s h := by
    rw [← hp]
    exact Submodule.subset_span (Or.inr rfl)
  obtain ⟨d, hd⟩ := pairOperator_mem_span (splitQuadraticForm K (s + 4)).polarBilin
    ((h.val : Mat K (s + 4)) *ᵥ firstVector K s)
    ((h.val : Mat K (s + 4)) *ᵥ secondVector K s)
    ((g.val : Mat K (s + 4)) *ᵥ firstVector K s)
    ((g.val : Mat K (s + 4)) *ᵥ secondVector K s) hu hv
  refine ⟨a * d, ?_⟩
  have he : Matrix.mulVecLin (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) =
      Matrix.mulVecLin (((h * highestRoot K s (a * d) * h⁻¹).val : Mat K (s + 4)) - 1) := by
    rw [conjugate_highestRoot_displacement_pairOperator,
      conjugate_highestRoot_displacement_pairOperator, hd, smul_smul]
  have hm : (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) =
      (((h * highestRoot K s (a * d) * h⁻¹).val : Mat K (s + 4)) - 1) := by
    ext i j
    have hx := congrFun (LinearMap.congr_fun he (Pi.single j 1)) i
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hx
  apply Subtype.ext
  apply Units.ext
  have hm' := congrArg (fun M : Mat K (s + 4) => M + 1) hm
  simpa only [sub_add_cancel] using hm'

private theorem conjugateRootLine_le_of_plane_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hp : conjugateRootPlane K s g = conjugateRootPlane K s h) :
    conjugateRootLine K s g ≤ conjugateRootLine K s h := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := (mem_highestRootLine_iff K s y).mp hy
  obtain ⟨b, hb⟩ := conjugate_root_element_of_plane_eq K s g h hp a
  refine ⟨highestRoot K s b, (mem_highestRootLine_iff K s _).mpr ⟨b, rfl⟩, ?_⟩
  change h * highestRoot K s b * h⁻¹ = g * highestRoot K s a * g⁻¹
  exact hb.symm

theorem conjugateRootLine_eq_of_plane_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hp : conjugateRootPlane K s g = conjugateRootPlane K s h) :
    conjugateRootLine K s g = conjugateRootLine K s h :=
  le_antisymm (conjugateRootLine_le_of_plane_eq K s g h hp)
    (conjugateRootLine_le_of_plane_eq K s h g hp.symm)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneRootLine
