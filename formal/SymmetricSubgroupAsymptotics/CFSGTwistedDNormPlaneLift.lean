import SymmetricSubgroupAsymptotics.CFSGTwistedDBasePoleCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairTailIsometry
import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicCoordinates

/-! A literal anisotropic-plane linear map extends by the identity on
all hyperbolic coordinates. Its action commutes with taking the SAME
fixed tail, providing the exact residual map for frame induction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLift
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDLinearParameters
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDFixedTailLinear
open CFSGTwistedDBasePoleCoordinates CFSGTwistedA2FixedField

def lift (n : ℕ) (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2) :
    fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q :=
  ((linearParameters n q).trans
    ((LinearEquiv.refl (fixedField q) (Fin (n + 1) → fixedField q)).prodCongr
      ((LinearEquiv.refl (fixedField q) (Fin (n + 1) → fixedField q)).prodCongr T))).trans
    (linearParameters n q).symm

theorem coordinates (n : ℕ) (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2) (v : fixedSpace n q) :
    linearParameters n q (lift n q T v) =
      ((linearParameters n q v).1,
        ((linearParameters n q v).2.1, T (linearParameters n q v).2.2)) :=
  (linearParameters n q).apply_symm_apply _

theorem quadratic (n : ℕ) (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2)
    (hT : ∀ a, normForm q (T a) = normForm q a) (v : fixedSpace n q) :
    fixedQuadraticForm n q (lift n q T v) = fixedQuadraticForm n q v := by
  have hN (a) : Algebra.norm (fixedField q) (T a) = Algebra.norm (fixedField q) a := by
    simpa only [normForm_apply] using hT a
  have hQ (x : fixedSpace n q) := quadratic_parameters n q (linearParameters n q x)
  simp only [LinearEquiv.symm_apply_apply] at hQ
  rw [hQ, hQ, coordinates, hN]

theorem tail_parameters (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace (n + 1) q) :
    linearParameters n q (tailLinear n q v) =
      ((fun i => (linearParameters (n + 1) q v).1 i.succ),
        ((fun i => (linearParameters (n + 1) q v).2.1 i.succ),
          (linearParameters (n + 1) q v).2.2)) := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    rfl
  · apply Prod.ext
    · funext i
      apply Subtype.ext
      rfl
    · rfl

theorem base_coordinates (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2) (v : fixedSpace 0 q) :
    basePoleEquiv q (lift 0 q T v) =
      ((basePoleEquiv q v).1, (T (basePoleEquiv q v).2.1, (basePoleEquiv q v).2.2)) := by
  exact congrArg (fun x : (Fin 1 → fixedField q) × ((Fin 1 → fixedField q) × q.Extension 2) =>
    (x.1 0, (x.2.2, x.2.1 0))) (coordinates 0 q T v)

theorem pole_coordinates (n : ℕ) (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2) (v : fixedSpace (n + 1) q) :
    poleEquiv n q (lift (n + 1) q T v) =
      (positiveHead n q v, (lift n q T (tailLinear n q v), negativeHead n q v)) := by
  apply Prod.ext
  · exact congrArg (fun x : (Fin (n + 2) → fixedField q) ×
      ((Fin (n + 2) → fixedField q) × q.Extension 2) => x.1 0)
        (coordinates (n + 1) q T v)
  · apply Prod.ext
    · apply (linearParameters n q).injective
      change linearParameters n q (tailLinear n q (lift (n + 1) q T v)) =
        linearParameters n q (lift n q T (tailLinear n q v))
      simp only [tail_parameters, coordinates]
    · exact congrArg (fun x : (Fin (n + 2) → fixedField q) ×
        ((Fin (n + 2) → fixedField q) × q.Extension 2) => x.2.1 0)
          (coordinates (n + 1) q T v)

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLift
