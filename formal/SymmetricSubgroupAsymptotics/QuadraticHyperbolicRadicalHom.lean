import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Group.TypeTags.Basic

/-! The quadratic hyperbolic shear is an injective additive-parameter
group, normalized by actual isometries of its tail. No recognition of
an ambient classical group is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalHom

open CFSGQuadraticHyperbolicShear
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

def parameterHom (Q : QuadraticForm K W) :
    Multiplicative W →* ((K × (W × K)) ≃ₗ[K] (K × (W × K))) where
  toFun z := transformEquiv Q z.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact transform_zero Q x
  map_mul' z t := by
    apply LinearEquiv.ext
    intro x
    exact (transform_comp Q z.toAdd t.toAdd x).symm

@[simp] theorem parameterHom_apply (Q : QuadraticForm K W)
    (z : Multiplicative W) (x : K × (W × K)) :
    parameterHom Q z x = transform Q z.toAdd x := rfl

theorem parameterHom_injective (Q : QuadraticForm K W) :
    Function.Injective (parameterHom Q) := by
  intro z t he
  have ht := congrArg (fun e : (K × (W × K)) ≃ₗ[K] (K × (W × K)) =>
    (e (0, (0, 1))).2.1) he
  change (0 : W) + (1 : K) • z.toAdd = 0 + (1 : K) • t.toAdd at ht
  have hz : z.toAdd = t.toAdd := by simpa only [one_smul, zero_add] using ht
  exact congrArg Multiplicative.ofAdd hz

/-- Extend the given actual tail equivalence, fixing both hyperbolic coordinates. -/
def levi (e : W ≃ₗ[K] W) : (K × (W × K)) ≃ₗ[K] (K × (W × K)) :=
  (LinearEquiv.refl K K).prodCongr (e.prodCongr (LinearEquiv.refl K K))

@[simp] theorem levi_apply (e : W ≃ₗ[K] W) (x : K × (W × K)) :
    levi e x = (x.1, (e x.2.1, x.2.2)) := rfl

theorem polar_preserved (Q : QuadraticForm K W) (e : W ≃ₗ[K] W)
    (he : ∀ w : W, Q (e w) = Q w) (v w : W) :
    QuadraticMap.polar Q (e v) (e w) = QuadraticMap.polar Q v w := by
  change Q (e v + e w) - Q (e v) - Q (e w) = Q (v + w) - Q v - Q w
  rw [← map_add, he, he, he]

/-- Exact covariance with the same tail isometry and the same parameter. -/
theorem levi_transform (Q : QuadraticForm K W) (e : W ≃ₗ[K] W)
    (he : ∀ w : W, Q (e w) = Q w) (z : W) (x : K × (W × K)) :
    levi e (transform Q z x) = transform Q (e z) (levi e x) := by
  apply Prod.ext
  · change x.1 - QuadraticMap.polar Q z x.2.1 - Q z * x.2.2 =
      x.1 - QuadraticMap.polar Q (e z) (e x.2.1) - Q (e z) * x.2.2
    rw [polar_preserved Q e he, he]
  · apply Prod.ext
    · change e (x.2.1 + x.2.2 • z) = e x.2.1 + x.2.2 • e z
      simp only [map_add, map_smul]
    · rfl

end SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalHom
