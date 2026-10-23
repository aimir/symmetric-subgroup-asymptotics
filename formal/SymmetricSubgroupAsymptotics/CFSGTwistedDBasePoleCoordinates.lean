import SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankFixedPairFrame
import Mathlib.LinearAlgebra.Pi

/-! The natural-rank-two fixed space is its literal first hyperbolic
pair plus the anisotropic quadratic-extension norm plane. These are
coordinates on the actual carrier, not a split-form replacement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDBasePoleCoordinates
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDLinearParameters
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSingularDimensionBound
open CFSGTwistedDAllRankFixedPairFrame CFSGTwistedA2FixedField
open CFSGOrthogonalDGenerationForkTorus

def basePoleEquiv (q : CFSG.PrimePower) :
    fixedSpace 0 q ≃ₗ[fixedField q] fixedField q × (q.Extension 2 × fixedField q) :=
  ((linearParameters 0 q).trans
    ((LinearEquiv.funUnique (Fin 1) (fixedField q) (fixedField q)).prodCongr
      ((LinearEquiv.funUnique (Fin 1) (fixedField q) (fixedField q)).prodCongr
        (LinearEquiv.refl (fixedField q) (q.Extension 2))))).trans
    ((LinearEquiv.refl (fixedField q) (fixedField q)).prodCongr
      (LinearEquiv.prodComm (fixedField q) (fixedField q) (q.Extension 2)))

theorem quadratic_inv (q : CFSG.PrimePower) (a b : fixedField q) (z : q.Extension 2) :
    fixedQuadraticForm 0 q ((basePoleEquiv q).symm (a, (z, b))) = a * b + normForm q z := by
  change fixedQuadraticForm 0 q
    ((linearParameters 0 q).symm ((fun _ => a), ((fun _ => b), z))) = _
  rw [quadratic_parameters, normForm_apply]
  change (∑ _ : Fin 1, a * b) + Algebra.norm (fixedField q) z =
    a * b + Algebra.norm (fixedField q) z
  rw [Fin.sum_univ_one]

theorem basePole_firstAxis (q : CFSG.PrimePower) :
    basePoleEquiv q (firstAxis 0 q) = (1, (0, 0)) := by
  apply Prod.ext
  · apply Subtype.ext
    change (Pi.single (Sum.inl (0 : Fin 2)) (1 : q.Extension 2) :
      CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inl 0) = 1
    exact Pi.single_eq_same _ _
  · apply Prod.ext
    · change (Pi.single (Sum.inl (0 : Fin 2)) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inl (last 0)) = 0
      have hn : Sum.inl (last 0) ≠ (Sum.inl (0 : Fin 2) : CFSGOrthogonalDSerreMatrices.Index 2) := by
        decide
      simp only [Pi.single_apply, if_neg hn]
    · apply Subtype.ext
      change (Pi.single (Sum.inl (0 : Fin 2)) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inr 0) = 0
      simp only [Pi.single_apply, Sum.inr_ne_inl, if_false]

theorem basePole_negativeFirst (q : CFSG.PrimePower) :
    basePoleEquiv q (negativeFirst 0 q) = (0, (0, 1)) := by
  apply Prod.ext
  · apply Subtype.ext
    change (Pi.single (Sum.inr (0 : Fin 2)) (1 : q.Extension 2) :
      CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inl 0) = 0
    simp only [Pi.single_apply, Sum.inl_ne_inr, if_false]
  · apply Prod.ext
    · change (Pi.single (Sum.inr (0 : Fin 2)) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inl (last 0)) = 0
      simp only [Pi.single_apply, Sum.inl_ne_inr, if_false]
    · apply Subtype.ext
      change (Pi.single (Sum.inr (0 : Fin 2)) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inr 0) = 1
      exact Pi.single_eq_same _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDBasePoleCoordinates
