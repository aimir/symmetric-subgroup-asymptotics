import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! The literal positive coordinate space is maximal totally singular
for the SAME bundled split Q. The SAME actual elementary matrices act
by their natural linear equivalences. No full isometry-group equality
or projective/component identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def positiveSpace (r : ℕ) : Submodule K (Index r → K) where
  carrier := {x | ∀ i : Fin r, x (Sum.inr i) = 0}
  zero_mem' := fun _ => rfl
  add_mem' := by intro x y hx hy i; simp only [Pi.add_apply, hx i, hy i, add_zero]
  smul_mem' := by intro c x hx i; simp only [Pi.smul_apply, hx i, smul_zero]

def positiveEquiv (r : ℕ) : (Fin r → K) ≃ₗ[K] positiveSpace K r where
  toFun x := ⟨Sum.elim x 0, fun _ => rfl⟩
  invFun x := leftPart K x.val
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact (x.property j).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact (zero_add (0 : K)).symm
  map_smul' c x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact (mul_zero c).symm

theorem positiveSpace_finrank (r : ℕ) : Module.finrank K (positiveSpace K r) = r := by
  simpa using (positiveEquiv K r).finrank_eq.symm

theorem naturalSpace_finrank (r : ℕ) : Module.finrank K (Index r → K) = 2 * r := by
  simp [Index, two_mul]

theorem positiveSpace_singular (r : ℕ) (x : positiveSpace K r) :
    splitQuadraticForm K r (x : Index r → K) = 0 := by
  rw [splitQuadraticForm_apply]
  change (∑ i : Fin r, x.val (Sum.inl i) * x.val (Sum.inr i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [x.property i, mul_zero]

theorem positiveSpace_self_orthogonal (r : ℕ) :
    LinearMap.BilinForm.orthogonal (splitQuadraticForm K r).polarBilin (positiveSpace K r) =
      positiveSpace K r := by
  ext x
  constructor
  · intro hx i
    have hp : Pi.single (Sum.inl i) (1 : K) ∈ positiveSpace K r := by
      intro j
      simp
    have h := hx _ hp
    change (splitQuadraticForm K r).polarBilin (Pi.single (Sum.inl i) 1) x = 0 at h
    rw [splitQuadraticForm_polar] at h
    simpa [polar, leftPart, rightPart, dotProduct, Pi.single_apply, eq_comm] using h
  · intro hx y hy
    change (splitQuadraticForm K r).polarBilin y x = 0
    rw [splitQuadraticForm_polar]
    change (∑ i : Fin r, y (Sum.inl i) * x (Sum.inr i)) +
      (∑ i : Fin r, x (Sum.inl i) * y (Sum.inr i)) = 0
    have h1 : (∑ i : Fin r, y (Sum.inl i) * x (Sum.inr i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hx i, mul_zero]
    have h2 : (∑ i : Fin r, x (Sum.inl i) * y (Sum.inr i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hy i, mul_zero]
    rw [h1, h2, add_zero]

def naturalLinearHom (r : ℕ) : elementaryRootGroup K r →*
    ((Index r → K) ≃ₗ[K] (Index r → K)) :=
  ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index r → K))).toMonoidHom).comp
      (elementaryRootGroup K r).subtype

theorem naturalLinearHom_apply (r : ℕ) (g : elementaryRootGroup K r) (x : Index r → K) :
    naturalLinearHom K r g x = (g.val : Mat K r) *ᵥ x := rfl

theorem naturalLinearHom_preserves_Q (s : ℕ) (g : elementaryRootGroup K (s + 4))
    (x : Index (s + 4) → K) :
    splitQuadraticForm K (s + 4) (naturalLinearHom K (s + 4) g x) =
      splitQuadraticForm K (s + 4) x :=
  elementary_preserves_bundledQ K s g x

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
