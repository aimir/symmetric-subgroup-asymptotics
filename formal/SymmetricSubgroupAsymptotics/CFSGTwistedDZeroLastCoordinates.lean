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
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDZeroLastCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGTwistedDFixedVectorCoordinates
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists
open CFSGTwistedDHyperbolicBlockCoordinates CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm

def blockVector (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v) :
    Index (s + 3) → fixedField q
  | Sum.inl i => ⟨v (Sum.inl i.castSucc), positive_fixed (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩
  | Sum.inr i => ⟨v (Sum.inr i.castSucc), negative_fixed (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩

theorem blockVector_val (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (x : Index (s + 3)) :
    ((blockVector s q v hv x : fixedField q) : q.Extension 2) = v (blockIndex (s + 3) x) := by
  cases x <;> rfl

theorem blockVector_ne_zero (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (s + 2))) = 0)
    (hn : v (Sum.inr (last (s + 2))) = 0) (hv0 : v ≠ 0) :
    blockVector s q v hv ≠ 0 := by
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

theorem blockVector_splitQ_zero (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (s + 2))) = 0)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0) :
    splitQ (fixedField q) (blockVector s q v hv) = 0 := by
  have hs : (∑ i : Fin (s + 3), v (Sum.inl i.castSucc) * v (Sum.inr i.castSucc)) = 0 := by
    rw [splitQuadraticForm_apply] at hQ
    change (∑ i : Fin (s + 4), v (Sum.inl i) * v (Sum.inr i)) = 0 at hQ
    rw [Fin.sum_univ_castSucc] at hQ
    have hp' : v (Sum.inl (Fin.last (s + 3))) = 0 := hp
    rw [hp', zero_mul, add_zero] at hQ
    exact hQ
  apply (fixedField q).subtype.injective
  change (fixedField q).subtype
    (∑ i : Fin (s + 3), blockVector s q v hv (Sum.inl i) *
      blockVector s q v hv (Sum.inr i)) = (fixedField q).subtype 0
  simpa only [map_sum, map_mul, map_zero, blockVector] using hs

end SymmetricSubgroupAsymptotics.CFSGTwistedDZeroLastCoordinates
