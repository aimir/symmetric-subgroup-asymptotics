import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleCoordinates
import SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalHom

/-! The full quadratic point shear on the SAME original odd-B natural
space. This file constructs its additive parameter hom and proves its
faithfulness; actual elementary-root membership is kept separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleShear

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOddQuadraticForm
open CFSGOrthogonalBOddPoleCoordinates CFSGQuadraticHyperbolicShear
variable (K : Type) [Field K]

def poleShear (h2 : (2 : K) ≠ 0) (n : ℕ) (z : Index n → K) :
    (Index (n + 1) → K) ≃ₗ[K] (Index (n + 1) → K) :=
  (coordinateEquiv K h2 n).trans
    ((transformEquiv (quadratic K n) z).trans (coordinateEquiv K h2 n).symm)

theorem coordinates_poleShear (h2 : (2 : K) ≠ 0) (n : ℕ)
    (z : Index n → K) (v : Index (n + 1) → K) :
    coordinates K n (poleShear K h2 n z v) =
      transform (quadratic K n) z (coordinates K n v) :=
  (coordinateEquiv K h2 n).apply_symm_apply _

theorem poleShear_zero_apply (h2 : (2 : K) ≠ 0) (n : ℕ) (v : Index (n + 1) → K) :
    poleShear K h2 n 0 v = v := by
  apply (coordinateEquiv K h2 n).injective
  change coordinates K n (poleShear K h2 n 0 v) = coordinates K n v
  rw [coordinates_poleShear, transform_zero]

theorem poleShear_add_apply (h2 : (2 : K) ≠ 0) (n : ℕ)
    (z t : Index n → K) (v : Index (n + 1) → K) :
    poleShear K h2 n (z + t) v = poleShear K h2 n z (poleShear K h2 n t v) := by
  apply (coordinateEquiv K h2 n).injective
  change coordinates K n (poleShear K h2 n (z + t) v) =
    coordinates K n (poleShear K h2 n z (poleShear K h2 n t v))
  rw [coordinates_poleShear, coordinates_poleShear, coordinates_poleShear]
  exact (transform_comp _ z t _).symm

def parameterHom (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Multiplicative (Index n → K) →* ((Index (n + 1) → K) ≃ₗ[K] (Index (n + 1) → K)) where
  toFun z := poleShear K h2 n z.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact poleShear_zero_apply K h2 n v
  map_mul' z t := by
    apply LinearEquiv.ext
    intro v
    exact poleShear_add_apply K h2 n z.toAdd t.toAdd v

@[simp] theorem parameterHom_apply (h2 : (2 : K) ≠ 0) (n : ℕ)
    (z : Multiplicative (Index n → K)) (v : Index (n + 1) → K) :
    parameterHom K h2 n z v = poleShear K h2 n z.toAdd v := rfl

theorem parameterHom_injective (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Function.Injective (parameterHom K h2 n) := by
  intro z t h
  apply QuadraticHyperbolicRadicalHom.parameterHom_injective (quadratic K n)
  apply LinearEquiv.ext
  intro x
  have he := congrArg (fun A : (Index (n + 1) → K) ≃ₗ[K] (Index (n + 1) → K) =>
    coordinateEquiv K h2 n (A ((coordinateEquiv K h2 n).symm x))) h
  dsimp only at he
  change coordinates K n (poleShear K h2 n z.toAdd ((coordinateEquiv K h2 n).symm x)) =
    coordinates K n (poleShear K h2 n t.toAdd ((coordinateEquiv K h2 n).symm x)) at he
  rw [coordinates_poleShear, coordinates_poleShear] at he
  change transform (quadratic K n) z.toAdd
      (coordinateEquiv K h2 n ((coordinateEquiv K h2 n).symm x)) =
    transform (quadratic K n) t.toAdd
      (coordinateEquiv K h2 n ((coordinateEquiv K h2 n).symm x)) at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

theorem poleShear_preserves_quadratic (h2 : (2 : K) ≠ 0) (n : ℕ)
    (z : Index n → K) (v : Index (n + 1) → K) :
    quadratic K (n + 1) (poleShear K h2 n z v) = quadratic K (n + 1) v := by
  rw [quadratic_coordinates K h2 n (poleShear K h2 n z v), coordinates_poleShear,
    transform_preserves, ← quadratic_coordinates K h2 n v]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleShear
