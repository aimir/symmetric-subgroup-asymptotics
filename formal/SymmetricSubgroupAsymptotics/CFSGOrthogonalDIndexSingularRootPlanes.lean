import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootPlaneImage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingPlane

/-! Every original root-plane label is an actual two-dimensional
totally Q-singular subspace, including characteristic two. This proves
admissibility of the original labels, not transitivity onto all polar
two-planes or a projective/building automorphism classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexRootPlaneImage CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexAlternatingPlane
variable (K : Type) [Field K]

def standardPlaneMap (s : ℕ) : K × K →ₗ[K] (Index (s + 4) → K) :=
  planeMap (firstVector K s) (secondVector K s)

theorem standardPlaneMap_injective (s : ℕ) : Function.Injective (standardPlaneMap K s) := by
  intro x y he
  apply Prod.ext
  · have h := congrFun he (Sum.inl 0)
    simpa [standardPlaneMap, planeMap, firstVector, secondVector, Pi.single_apply,
      zero_ne_second, Ne.symm (zero_ne_second s)] using h
  · have h := congrFun he (Sum.inl (secondIndex s))
    simpa [standardPlaneMap, planeMap, firstVector, secondVector, Pi.single_apply,
      zero_ne_second, Ne.symm (zero_ne_second s)] using h

theorem standardPlaneMap_range (s : ℕ) :
    (standardPlaneMap K s).range = standardRootPlane K s := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact (standardRootPlane K s).add_mem
      ((standardRootPlane K s).smul_mem p.1 (Submodule.subset_span (Or.inl rfl)))
      ((standardRootPlane K s).smul_mem p.2 (Submodule.subset_span (Or.inr rfl)))
  · intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    exact ⟨(a, b), rfl⟩

theorem standardRootPlane_finrank (s : ℕ) : Module.finrank K (standardRootPlane K s) = 2 := by
  rw [← standardPlaneMap_range]
  simpa using LinearMap.finrank_range_of_inj (f := standardPlaneMap K s)
    (standardPlaneMap_injective K s)

theorem standardRootPlane_le_positive (s : ℕ) :
    standardRootPlane K s ≤ positiveSpace K (s + 4) := by
  apply Submodule.span_le.mpr
  rintro x (rfl | rfl) <;> intro j <;> simp [firstVector, secondVector]

theorem conjugateRootPlane_eq_map_standard (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    conjugateRootPlane K s g =
      (standardRootPlane K s).map (Matrix.mulVecLin (g.val : Mat K (s + 4))) := by
  rw [standardRootPlane, Submodule.map_span, Set.image_pair]
  rfl

theorem conjugateRootPlane_finrank (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    Module.finrank K (conjugateRootPlane K s g) = 2 := by
  rw [conjugateRootPlane_eq_map_standard]
  change Module.finrank K ((standardRootPlane K s).map
    (naturalLinearHom K (s + 4) g).toLinearMap) = 2
  rw [LinearEquiv.finrank_map_eq, standardRootPlane_finrank]

theorem conjugateRootPlane_singular (s : ℕ) (g : elementaryRootGroup K (s + 4))
    (x : Index (s + 4) → K) (hx : x ∈ conjugateRootPlane K s g) :
    splitQuadraticForm K (s + 4) x = 0 := by
  rw [conjugateRootPlane_eq_map_standard] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, elementary_preserves_bundledQ]
  exact positiveSpace_singular K (s + 4) ⟨y, standardRootPlane_le_positive K s hy⟩

theorem conjugateRootPlane_polar_zero (s : ℕ) (g : elementaryRootGroup K (s + 4))
    (x y : Index (s + 4) → K) (hx : x ∈ conjugateRootPlane K s g)
    (hy : y ∈ conjugateRootPlane K s g) :
    (splitQuadraticForm K (s + 4)).polarBilin x y = 0 := by
  change splitQuadraticForm K (s + 4) (x + y) - splitQuadraticForm K (s + 4) x -
    splitQuadraticForm K (s + 4) y = 0
  rw [conjugateRootPlane_singular K s g (x + y) ((conjugateRootPlane K s g).add_mem hx hy),
    conjugateRootPlane_singular K s g x hx, conjugateRootPlane_singular K s g y hy]
  ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularRootPlanes
