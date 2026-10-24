import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergOperators
import SymmetricSubgroupAsymptotics.CFSGSymplecticAllNaturalTransvections

/-! Actual original elementary words realize the uniform Heisenberg
operators. Equality is proved on natural vectors, where the literal
matrix action is faithful. No parabolic recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergWords

open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticHeisenbergOperators
variable (K : Type) [Field K]

theorem elementary_ext_of_mulVec (n : ℕ) (g h : elementaryRootGroup K n)
    (he : ∀ x : Index n → K, (g.val : Mat K n) *ᵥ x = (h.val : Mat K n) *ᵥ x) : g = h := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hcol := congrFun (he (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hcol

def naturalElement (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) (a : K) :
    elementaryRootGroup K (r + 1) :=
  if hv : v = 0 then 1 else
    Classical.choose (exists_elementary_natural_transvection r hr v hv a)

theorem naturalElement_apply (r : ℕ) (hr : 0 < r)
    (v x : Index (r + 1) → K) (a : K) :
    ((naturalElement K r hr v a).val : Mat K (r + 1)) *ᵥ x =
      transvection (r + 1) v a x := by
  classical
  by_cases hv : v = 0
  · simp only [naturalElement, dif_pos hv, hv, transvection_apply,
      pairing_zero_left, mul_zero, zero_smul, add_zero]
    exact Matrix.one_mulVec x
  · simpa only [naturalElement, dif_neg hv] using
      (Classical.choose_spec (exists_elementary_natural_transvection r hr v hv a) x)

def shearElement (r : ℕ) (hr : 0 < r) (e v : Index (r + 1) → K) (z : K) :
    elementaryRootGroup K (r + 1) :=
  naturalElement K r hr (e + v) 1 * naturalElement K r hr v (-1) *
    naturalElement K r hr e (z - 1)

theorem shearElement_apply (r : ℕ) (hr : 0 < r)
    (e v x : Index (r + 1) → K) (z : K) :
    ((shearElement K r hr e v z).val : Mat K (r + 1)) *ᵥ x =
      shear (r + 1) e v z x := by
  change (((naturalElement K r hr (e + v) 1).val : Mat K (r + 1)) *
      ((naturalElement K r hr v (-1)).val : Mat K (r + 1)) *
      ((naturalElement K r hr e (z - 1)).val : Mat K (r + 1))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    naturalElement_apply, naturalElement_apply, naturalElement_apply]
  rfl

theorem shearElement_mul (r : ℕ) (hr : 0 < r)
    (e v w : Index (r + 1) → K) (z t : K)
    (hev : pairing (r + 1) e v = 0) (hew : pairing (r + 1) e w = 0) :
    shearElement K r hr e v z * shearElement K r hr e w t =
      shearElement K r hr e (v + w) (z + t + pairing (r + 1) v w) := by
  apply elementary_ext_of_mulVec K
  intro x
  change (((shearElement K r hr e v z).val : Mat K (r + 1)) *
      ((shearElement K r hr e w t).val : Mat K (r + 1))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, shearElement_apply, shearElement_apply, shearElement_apply]
  exact congrArg (fun A : (Index (r + 1) → K) ≃ₗ[K] (Index (r + 1) → K) => A x)
    (shear_mul (r + 1) e v w z t hev hew)

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergWords
