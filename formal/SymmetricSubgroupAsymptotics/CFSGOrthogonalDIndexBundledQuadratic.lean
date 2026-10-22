import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The checked literal split Q is bundled as an actual quadratic form.
Its actual polar form is nondegenerate in every characteristic. These
are direct coordinate facts, not a classical-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexPolarForm
variable (K : Type) [Field K]

def splitQuadraticForm (r : ℕ) : QuadraticForm K (Index r → K) :=
  ∑ i : Fin r, QuadraticMap.proj (Sum.inl i) (Sum.inr i)

theorem splitQuadraticForm_apply (r : ℕ) (x : Index r → K) :
    splitQuadraticForm K r x = splitQ K x := by
  simp only [splitQuadraticForm, QuadraticMap.sum_apply, QuadraticMap.proj_apply]
  rfl

theorem splitQuadraticForm_polar (r : ℕ) (x y : Index r → K) :
    (splitQuadraticForm K r).polarBilin x y = polar K x y := by
  change splitQuadraticForm K r (x + y) - splitQuadraticForm K r x -
    splitQuadraticForm K r y = polar K x y
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply, splitQuadraticForm_apply,
    splitQ_add]
  ring

theorem splitQuadraticForm_nondegenerate (r : ℕ) :
    (splitQuadraticForm K r).polarBilin.Nondegenerate := by
  have hsep : ∀ x : Index r → K,
      (∀ y, (splitQuadraticForm K r).polarBilin x y = 0) → x = 0 := by
    intro x hx
    funext i
    cases i with
    | inl j =>
      have h := hx (Pi.single (Sum.inr j) 1)
      rw [splitQuadraticForm_polar] at h
      simpa [polar, leftPart, rightPart, dotProduct, Pi.single_apply, eq_comm] using h
    | inr j =>
      have h := hx (Pi.single (Sum.inl j) 1)
      rw [splitQuadraticForm_polar] at h
      simpa [polar, leftPart, rightPart, dotProduct, Pi.single_apply, eq_comm] using h
  refine ⟨hsep, fun x hx => hsep x (fun y => ?_)⟩
  have h := hx y
  rw [splitQuadraticForm_polar] at h ⊢
  simpa only [polar, add_comm] using h

theorem elementary_preserves_bundledQ (s : ℕ) (g : elementaryRootGroup K (s + 4))
    (x : Index (s + 4) → K) :
    splitQuadraticForm K (s + 4) ((g.val : Mat K (s + 4)) *ᵥ x) =
      splitQuadraticForm K (s + 4) x := by
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
  exact elementary_preserves_splitQ K s g x

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
