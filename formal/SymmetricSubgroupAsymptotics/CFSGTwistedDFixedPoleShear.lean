import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPolePolar
import SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalHom

/-! Full pole shears on the SAME defining-fixed twisted-D spaces.
The actual anisotropic tail is retained in every rank, including the
rank-two tail. Elementary-relative membership is a separate obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShear

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPolePolar CFSGTwistedA2FixedField CFSGQuadraticHyperbolicShear

def poleShear (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedSpace (n + 1) q :=
  (poleEquiv n q).trans
    ((transformEquiv (fixedQuadraticForm n q) z).trans (poleEquiv n q).symm)

theorem poleEquiv_poleShear (n : ℕ) (q : CFSG.PrimePower)
    (z : fixedSpace n q) (v : fixedSpace (n + 1) q) :
    poleEquiv n q (poleShear n q z v) =
      transform (fixedQuadraticForm n q) z (poleEquiv n q v) :=
  (poleEquiv n q).apply_symm_apply _

theorem poleShear_zero_apply (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) : poleShear n q 0 v = v := by
  apply (poleEquiv n q).injective
  rw [poleEquiv_poleShear, transform_zero]

theorem poleShear_add_apply (n : ℕ) (q : CFSG.PrimePower)
    (z t : fixedSpace n q) (v : fixedSpace (n + 1) q) :
    poleShear n q (z + t) v = poleShear n q z (poleShear n q t v) := by
  apply (poleEquiv n q).injective
  rw [poleEquiv_poleShear, poleEquiv_poleShear, poleEquiv_poleShear]
  exact (transform_comp _ z t _).symm

def parameterHom (n : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedSpace n q) →*
      (fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedSpace (n + 1) q) where
  toFun z := poleShear n q z.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact poleShear_zero_apply n q v
  map_mul' z t := by
    apply LinearEquiv.ext
    intro v
    exact poleShear_add_apply n q z.toAdd t.toAdd v

@[simp] theorem parameterHom_apply (n : ℕ) (q : CFSG.PrimePower)
    (z : Multiplicative (fixedSpace n q)) (v : fixedSpace (n + 1) q) :
    parameterHom n q z v = poleShear n q z.toAdd v := rfl

theorem parameterHom_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (parameterHom n q) := by
  intro z t h
  apply QuadraticHyperbolicRadicalHom.parameterHom_injective (fixedQuadraticForm n q)
  apply LinearEquiv.ext
  intro x
  have he := congrArg (fun A : fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedSpace (n + 1) q =>
    poleEquiv n q (A ((poleEquiv n q).symm x))) h
  dsimp only at he
  change poleEquiv n q (poleShear n q z.toAdd ((poleEquiv n q).symm x)) =
    poleEquiv n q (poleShear n q t.toAdd ((poleEquiv n q).symm x)) at he
  rw [poleEquiv_poleShear, poleEquiv_poleShear, LinearEquiv.apply_symm_apply] at he
  exact he

theorem poleShear_preserves_quadratic (n : ℕ) (q : CFSG.PrimePower)
    (z : fixedSpace n q) (v : fixedSpace (n + 1) q) :
    fixedQuadraticForm (n + 1) q (poleShear n q z v) = fixedQuadraticForm (n + 1) q v := by
  have hQ : ∀ w : fixedSpace (n + 1) q, fixedQuadraticForm (n + 1) q w =
      norm (fixedQuadraticForm n q) (poleEquiv n q w) := quadratic_coordinates n q
  rw [hQ, poleEquiv_poleShear, transform_preserves, ← hQ]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShear
