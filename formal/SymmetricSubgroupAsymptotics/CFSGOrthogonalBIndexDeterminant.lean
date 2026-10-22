import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.CharP.Reduced

/-! Every actual B root has determinant one in positive characteristic.
Its additive parameter has exponent p, while Frobenius is injective on
the field. This proves determinant one on the SAME generated subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexDeterminant
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

include p in
private theorem additive_to_units_eq_one (f : Multiplicative K →* Kˣ) (a : Multiplicative K) :
    f a = 1 := by
  have hp : (p : K) = 0 := CharP.cast_eq_zero K p
  have ha : a ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one, nsmul_eq_mul, hp, zero_mul]
  have hfp : (f a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  apply Units.ext
  apply frobenius_inj K p
  change (f a : K) ^ p = (1 : K) ^ p
  have h := congrArg (fun u : Kˣ => (u : K)) hfp
  change (f a : K) ^ p = 1 at h
  exact h.trans (one_pow p).symm

def determinantHom (r : ℕ) : elementaryRootGroup K r →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp (elementaryRootGroup K r).subtype

include p in
theorem determinantHom_eq_one (r : ℕ) (g : elementaryRootGroup K r) :
    determinantHom K r g = 1 := by
  have hroot (neg : Bool) (i : Fin r) (a : K) :
      determinantHom K r (rootElement K r neg i a) = 1 := by
    let f : Multiplicative K →* elementaryRootGroup K r := {
      toFun := fun a => rootElement K r neg i a.toAdd
      map_one' := rootElement_zero K r neg i
      map_mul' := fun a b => rootElement_add K r neg i a.toAdd b.toAdd }
    exact additive_to_units_eq_one K p ((determinantHom K r).comp f) (Multiplicative.ofAdd a)
  have hle : Subgroup.closure
      {u : elementaryRootGroup K r | ∃ neg i a, u = rootElement K r neg i a} ≤
      (determinantHom K r).ker := by
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨neg, i, a, rfl⟩
    exact hroot neg i a
  rw [rootElements_generate] at hle
  exact hle (Subgroup.mem_top g)

include p in
theorem elementary_det_eq_one (r : ℕ) (g : elementaryRootGroup K r) :
    (g.val : Mat K r).det = 1 :=
  congrArg (fun u : Kˣ => (u : K)) (determinantHom_eq_one K p r g)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexDeterminant
