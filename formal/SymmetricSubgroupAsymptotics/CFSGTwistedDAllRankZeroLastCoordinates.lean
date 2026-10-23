import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockCoordinates
import Mathlib.Algebra.BigOperators.Fin

/-! After the last conjugate pair vanishes, the remaining fixed-vector
coordinates are a literal vector over the actual fixed field. Its
nonzeroness and split quadratic norm are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGTwistedDFixedVectorCoordinates
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists
open CFSGTwistedDHyperbolicBlockCoordinates CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm

def blockVector (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v) :
    Index (n + 2) → fixedField q
  | Sum.inl i => ⟨v (Sum.inl i.castSucc), positive_fixed (q.Extension 2) (n + 1)
      (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩
  | Sum.inr i => ⟨v (Sum.inr i.castSucc), negative_fixed (q.Extension 2) (n + 1)
      (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩

theorem blockVector_val (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (x : Index (n + 2)) :
    ((blockVector n q v hv x : fixedField q) : q.Extension 2) = v (blockIndex (n + 2) x) := by
  cases x <;> rfl

theorem blockVector_ne_zero (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (n + 1))) = 0)
    (hn : v (Sum.inr (last (n + 1))) = 0) (hv0 : v ≠ 0) :
    blockVector n q v hv ≠ 0 := by
  intro hz
  apply hv0
  funext x
  cases x with
  | inl i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h := congrArg (fun z : fixedField q => (z : q.Extension 2))
        (congrFun hz (Sum.inl j))
      exact h
    · exact hp
  | inr i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h := congrArg (fun z : fixedField q => (z : q.Extension 2))
        (congrFun hz (Sum.inr j))
      exact h
    · exact hn

theorem blockVector_splitQ_zero (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (n + 1))) = 0)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0) :
    splitQ (fixedField q) (blockVector n q v hv) = 0 := by
  have hs : (∑ i : Fin (n + 2), v (Sum.inl i.castSucc) * v (Sum.inr i.castSucc)) = 0 := by
    rw [splitQuadraticForm_apply] at hQ
    change (∑ i : Fin (n + 3), v (Sum.inl i) * v (Sum.inr i)) = 0 at hQ
    rw [Fin.sum_univ_castSucc] at hQ
    have hp' : v (Sum.inl (Fin.last (n + 2))) = 0 := hp
    rw [hp', zero_mul, add_zero] at hQ
    exact hQ
  apply (fixedField q).subtype.injective
  change (fixedField q).subtype
    (∑ i : Fin (n + 2), blockVector n q v hv (Sum.inl i) *
      blockVector n q v hv (Sum.inr i)) = (fixedField q).subtype 0
  simpa only [map_sum, map_mul, map_zero, blockVector] using hs

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastCoordinates
