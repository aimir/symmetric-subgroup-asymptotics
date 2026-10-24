import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPoleSeed
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShear
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTailEmbedding
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular

/-! The actual all-rank long-root seed is exactly the full pole shear
at its singular tail parameter, on the literal defining-fixed carrier.
The natural-rank-three base and characteristic two remain included. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleSeedAction

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedTailLinear CFSGTwistedDFixedPoleShear
open CFSGTwistedDAllRankPoleSeed CFSGTwistedDHighestPairOperator
open CFSGTwistedDRelativeTailEmbedding CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGOrthogonalDIndexTailCoordinates CFSGQuadraticHyperbolicShear

theorem seedVector_polar_val (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    (((fixedQuadraticForm n q).polarBilin (seedVector n q) z : fixedField q) : q.Extension 2) =
      z.val (Sum.inr (pen n)) := by
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl (pen n)) 1) z.val = _
  exact polar_positive_basis (q.Extension 2) (n + 2) (pen n) z.val

theorem poleEquiv_seedElement (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) :
    poleEquiv n q (fixedLinearHom (n + 1) q (seedElement n q) v) =
      transform (fixedQuadraticForm n q) (seedVector n q) (poleEquiv n q v) := by
  have hp : (0 : Fin (n + 3)) ≠ pen (n + 1) := by
    intro he
    have hh := congrArg Fin.val he
    change 0 = n + 1 at hh
    omega
  apply Prod.ext
  · change positiveHead n q (fixedLinearHom (n + 1) q (seedElement n q) v) =
      positiveHead n q v - QuadraticMap.polar (fixedQuadraticForm n q)
        (seedVector n q) (tailLinear n q v) -
          fixedQuadraticForm n q (seedVector n q) * negativeHead n q v
    rw [seedVector_singular, zero_mul, sub_zero, ← QuadraticMap.polarBilin_apply_apply]
    apply Subtype.ext
    change (((seedElement n q).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val) (Sum.inl 0) =
      v.val (Sum.inl 0) -
        (((fixedQuadraticForm n q).polarBilin (seedVector n q) (tailLinear n q v) : fixedField q) : q.Extension 2)
    rw [seedVector_polar_val, seedElement_apply]
    change ((v.val - v.val (Sum.inr (pen (n + 1))) •
        (Pi.single (Sum.inl 0) (1 : q.Extension 2) : Index (n + 3) → q.Extension 2) +
      v.val (Sum.inr 0) •
        (Pi.single (Sum.inl (pen (n + 1))) (1 : q.Extension 2) : Index (n + 3) → q.Extension 2) :
          Index (n + 3) → q.Extension 2)) (Sum.inl 0) =
        v.val (Sum.inl 0) - v.val (Sum.inr ((pen n).succ))
    rw [pen_succ]
    simp [Pi.single_apply, hp]
  · apply Prod.ext
    · apply Subtype.ext
      funext i
      change (((seedElement n q).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val)
          (tailIndex (n + 2) i) =
        v.val (tailIndex (n + 2) i) + v.val (Sum.inr 0) *
          (Pi.single (Sum.inl (pen n)) (1 : q.Extension 2) : Index (n + 2) → q.Extension 2) i
      rw [seedElement_apply]
      rw [← pen_succ n]
      cases i with
      | inl i => simp [tailIndex, Pi.single_apply, Fin.succ_inj]
      | inr i => simp [tailIndex]
    · apply Subtype.ext
      change (((seedElement n q).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val) (Sum.inr 0) =
        v.val (Sum.inr 0)
      rw [seedElement_apply]
      simp

theorem seedElement_is_poleShear (n : ℕ) (q : CFSG.PrimePower) :
    fixedLinearHom (n + 1) q (seedElement n q) =
      parameterHom n q (Multiplicative.ofAdd (seedVector n q)) := by
  apply LinearEquiv.ext
  intro v
  apply (poleEquiv n q).injective
  rw [poleEquiv_seedElement]
  exact (poleEquiv_poleShear n q (seedVector n q) v).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleSeedAction
