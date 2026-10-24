import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShear
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTailEmbedding
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticAction

/-! The actual all-rank relative tail embedding acts on literal fixed
pole coordinates by the SAME fixed-field natural tail action. Hence it
intertwines the full shears without a new form-recognition hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleTailAction

open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticAction CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPoleShear CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeTailEmbedding CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexTailCoordinates

theorem poleEquiv_tail (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace (n + 1) q) :
    poleEquiv n q (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v) =
      QuadraticHyperbolicRadicalHom.levi (fixedLinearHom n q g) (poleEquiv n q v) := by
  apply Prod.ext
  · apply Subtype.ext
    change (((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val)
      (Sum.inl 0) = v.val (Sum.inl 0)
    exact head_positive n q g v.val
  · apply Prod.ext
    · apply Subtype.ext
      change tailRestriction (q.Extension 2) (n + 2)
          (((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val) =
        (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ tailRestriction (q.Extension 2) (n + 2) v.val
      exact tail_action n q g v.val
    · apply Subtype.ext
      change (((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val)
        (Sum.inr 0) = v.val (Sum.inr 0)
      exact head_negative n q g v.val

theorem tail_poleShear_intertwine (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (z : fixedSpace n q) (v : fixedSpace (n + 1) q) :
    fixedLinearHom (n + 1) q (tailRelativeHom n q g) (poleShear n q z v) =
      poleShear n q (fixedLinearHom n q g z)
        (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v) := by
  apply (poleEquiv n q).injective
  rw [poleEquiv_tail, poleEquiv_poleShear, poleEquiv_poleShear, poleEquiv_tail]
  exact QuadraticHyperbolicRadicalHom.levi_transform
    (fixedQuadraticForm n q) (fixedLinearHom n q g)
    (fixedLinearHom_preserves_Q n q g) z (poleEquiv n q v)

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleTailAction
