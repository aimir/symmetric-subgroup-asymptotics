import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankConjugateFork
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDHighestPairOperator
import Mathlib.Data.Matrix.Basis

/-! One literal fixed-field long-root seed for every twisted-D pole
radical, including the natural-rank-three ambient group. The tail seed
is its last split positive axis, not its anisotropic final coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPoleSeed

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedA2FixedField
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHighestPairOperator
open CFSGTwistedDAllRankPairedWeyl CFSGTwistedDA2MatrixWitness
open CFSGOrthogonalDIndexBundledQuadratic

def seedVector (n : ℕ) (q : CFSG.PrimePower) : fixedSpace n q :=
  positiveBasis n q (pen n) (pen_ne_last n)

theorem seedVector_nonzero (n : ℕ) (q : CFSG.PrimePower) : seedVector n q ≠ 0 := by
  intro he
  have hh := congrArg (fun v : fixedSpace n q => v.val (Sum.inl (pen n))) he
  change (Pi.single (Sum.inl (pen n)) (1 : q.Extension 2) : Index (n + 2) → q.Extension 2)
    (Sum.inl (pen n)) = 0 at hh
  exact one_ne_zero (by simpa only [Pi.single_eq_same] using hh)

theorem seedVector_singular (n : ℕ) (q : CFSG.PrimePower) :
    fixedQuadraticForm n q (seedVector n q) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, splitQuadraticForm_apply]
  change (∑ i : Fin (n + 2),
    (Pi.single (Sum.inl (pen n)) (1 : q.Extension 2) : Index (n + 2) → q.Extension 2) (Sum.inl i) *
    (Pi.single (Sum.inl (pen n)) (1 : q.Extension 2) : Index (n + 2) → q.Extension 2) (Sum.inr i)) = 0
  simp only [Pi.single_apply, Sum.inr_ne_inl, if_false, mul_zero, Finset.sum_const_zero]

private theorem head_ne_pen (n : ℕ) : (0 : Fin (n + 3)) ≠ pen (n + 1) := by
  intro he
  have hh := congrArg Fin.val he
  change 0 = n + 1 at hh
  omega

private theorem head_ne_last (n : ℕ) : (0 : Fin (n + 3)) ≠ last (n + 1) := by
  intro he
  have hh := congrArg Fin.val he
  change 0 = n + 2 at hh
  omega

private theorem head_ne_chain_end (n : ℕ) : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
  intro he
  have hh := congrArg Fin.val he
  change 0 = n + 1 at hh
  omega

private def retainedChain (n : ℕ) (q : CFSG.PrimePower) : relativeRootGroup (n + 1) q :=
  ⟨(chain (q.Extension 2) (n + 3) (0 : Fin (n + 2)).castSucc
      (Fin.last (n + 1)).castSucc
      ((Fin.castSucc_injective (n + 2)).ne (head_ne_chain_end n)) 1).val,
    CFSGTwistedDAllRankChainLift.chain_mem (n + 1) q 0 (Fin.last (n + 1))
      (head_ne_chain_end n) 1⟩

def seedElement (n : ℕ) (q : CFSG.PrimePower) : relativeRootGroup (n + 1) q :=
  weyl (n + 1) q * retainedChain n q * (weyl (n + 1) q)⁻¹

theorem seedElement_val (n : ℕ) (q : CFSG.PrimePower) :
    ((seedElement n q).val : Mat (q.Extension 2) (n + 3)) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr (pen (n + 1))) (-1) -
        Matrix.single (Sum.inl (pen (n + 1))) (Sum.inr 0) (-1) := by
  have h := CFSGTwistedDAllRankConjugateFork.conjugation_positive (n + 1) q
    0 (head_ne_pen n) (head_ne_last n) (-1)
  simpa only [seedElement, retainedChain, Subgroup.coe_mul, Subgroup.coe_inv,
    neg_neg, pen] using h

private theorem single_action {K : Type} [Field K] {r : ℕ}
    (i j : Index r) (a : K) (v : Index r → K) :
    Matrix.single i j a *ᵥ v = (a * v j) • Pi.single i 1 := by
  rw [Matrix.single_mulVec]
  funext x
  by_cases hx : x = i
  · subst x
    simp
  · simp [Function.update_apply, Pi.single_apply, hx]

theorem seedElement_apply (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2) :
    ((seedElement n q).val : Mat (q.Extension 2) (n + 3)) *ᵥ v =
      v - v (Sum.inr (pen (n + 1))) • Pi.single (Sum.inl 0) 1 +
        v (Sum.inr 0) • Pi.single (Sum.inl (pen (n + 1))) 1 := by
  rw [seedElement_val]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, single_action,
    neg_one_mul, neg_smul]
  abel

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPoleSeed
