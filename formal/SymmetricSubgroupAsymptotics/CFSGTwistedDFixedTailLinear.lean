import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates

/-! Literal first-pair/tail linear coordinates over the actual fixed
field. This is a hyperbolic first pair plus the SAME smaller fixed
quadratic space, without dividing by two or asserting a named form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailLinear
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedA2FixedField CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexTailCoordinates CFSGSplitQuadraticPoleCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGTwistedDFixedVectorCoordinates
open CFSGOrthogonalDGenerationForkTorus

private theorem zero_ne_last (n : ℕ) : (0 : Fin (n + 3)) ≠ last (n + 1) := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = n + 2 at hv
  omega

def positiveHead (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace (n + 1) q →ₗ[fixedField q] fixedField q where
  toFun v := ⟨v.val (Sum.inl 0), positive_fixed _ _ _ v.val v.property 0 (zero_ne_last n)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def negativeHead (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace (n + 1) q →ₗ[fixedField q] fixedField q where
  toFun v := ⟨v.val (Sum.inr 0), negative_fixed _ _ _ v.val v.property 0 (zero_ne_last n)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tailLinear (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace (n + 1) q →ₗ[fixedField q] fixedSpace n q where
  toFun v := ⟨tailRestriction (q.Extension 2) (n + 2) v.val, by
    change vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2)
      (v.val ∘ tailIndex (n + 2)) = v.val ∘ tailIndex (n + 2)
    rw [CFSGTwistedDTailTwist.vectorTwist_tail, v.property]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def poleEquiv (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedField q × (fixedSpace n q × fixedField q) where
  toFun v := (positiveHead n q v, (tailLinear n q v, negativeHead n q v))
  invFun x := ⟨fromCoordinates (q.Extension 2) (n + 2)
      ((x.1 : q.Extension 2), (x.2.1.val, (x.2.2 : q.Extension 2))),
    CFSGTwistedDFixedPoleCharts.fromCoordinates_fixed n q _ _ x.1.property x.2.2.property
      ⟨x.2.1.val, x.2.1.property⟩⟩
  left_inv v := by
    apply Subtype.ext
    exact from_coordinates (q.Extension 2) (n + 2) v.val
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Prod.ext
      · apply Subtype.ext
        funext i
        cases i <;> rfl
      · apply Subtype.ext
        rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quadratic_coordinates (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace (n + 1) q) :
    fixedQuadraticForm (n + 1) q v =
      positiveHead n q v * negativeHead n q v + fixedQuadraticForm n q (tailLinear n q v) := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  change splitQuadraticForm (q.Extension 2) (n + 3) v.val =
    v.val (Sum.inl 0) * v.val (Sum.inr 0) +
      splitQuadraticForm (q.Extension 2) (n + 2) (tailRestriction (q.Extension 2) (n + 2) v.val)
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
  change (∑ i : Fin (n + 3), v.val (Sum.inl i) * v.val (Sum.inr i)) = _
  rw [Fin.sum_univ_succ]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailLinear
