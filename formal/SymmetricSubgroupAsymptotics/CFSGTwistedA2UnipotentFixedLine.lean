import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FieldWitness

/-! The literal norm-constrained upper-unipotent arrays fix exactly the
first natural coordinate line. An actual root-transporting matrix must
therefore preserve that line, without a whole-unitary-group premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGTwistedA2FieldWitness CFSGTwistedA2TraceFibers

theorem upperArrays_fixed_iff (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (v : Fin 3 → q.Extension 2) :
    (∀ a b, NormCondition (definingFieldAutomorphism q 2) a b →
      (upperArray (definingFieldAutomorphism q 2) a b).mulVec v = v) ↔
        v 1 = 0 ∧ v 2 = 0 := by
  let σ := definingFieldAutomorphism q 2
  constructor
  · intro hv
    obtain ⟨t, a, ht, hts, _, _, _⟩ := exists_skew_and_fixed_scalar q hq
    have hzero : NormCondition σ 0 t := by
      change t + t ^ q.order = (0 : q.Extension 2) * σ 0
      rw [hts]
      simp
    have h0 := congrArg (fun w : Fin 3 → q.Extension 2 => w 0) (hv 0 t hzero)
    have h0' : v 0 + t * v 2 = v 0 := by
      simpa [upperArray, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
    have ht2 : t * v 2 = 0 := add_eq_left.mp h0'
    have hv2 : v 2 = 0 := (mul_eq_zero.mp ht2).resolve_left ht
    obtain ⟨b, hb⟩ := exists_trace_eq_norm q hq 1
    have h1 := congrArg (fun w : Fin 3 → q.Extension 2 => w 0) (hv 1 b hb)
    have h1' : v 0 + v 1 = v 0 := by
      simpa [upperArray, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2] using h1
    exact ⟨add_eq_left.mp h1', hv2⟩
  · rintro ⟨hv1, hv2⟩ a b _
    ext i
    fin_cases i <;>
      simp [upperArray, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2]

def firstBasisVector (q : CFSG.PrimePower) : Fin 3 → q.Extension 2 := ![1, 0, 0]

theorem first_column_zero_of_upper_transport (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (A : Mat (q.Extension 2) 2)
    (hA : ∀ a b, NormCondition (definingFieldAutomorphism q 2) a b →
      ∃ c d, NormCondition (definingFieldAutomorphism q 2) c d ∧
        upperArray (definingFieldAutomorphism q 2) a b * A =
          A * upperArray (definingFieldAutomorphism q 2) c d) : A 1 0 = 0 ∧ A 2 0 = 0 := by
  let e := firstBasisVector q
  have he (a b : q.Extension 2) (hab : NormCondition (definingFieldAutomorphism q 2) a b) :
      (upperArray (definingFieldAutomorphism q 2) a b).mulVec e = e :=
    (upperArrays_fixed_iff q hq e).mpr (by simp [e, firstBasisVector]) a b hab
  have hf : ∀ a b, NormCondition (definingFieldAutomorphism q 2) a b →
      (upperArray (definingFieldAutomorphism q 2) a b).mulVec (A.mulVec e) = A.mulVec e := by
    intro a b hab
    obtain ⟨c, d, hcd, hm⟩ := hA a b hab
    calc
      _ = (upperArray (definingFieldAutomorphism q 2) a b * A).mulVec e :=
        Matrix.mulVec_mulVec _ _ _
      _ = (A * upperArray (definingFieldAutomorphism q 2) c d).mulVec e :=
        congrArg (fun M : Mat (q.Extension 2) 2 => M.mulVec e) hm
      _ = A.mulVec ((upperArray (definingFieldAutomorphism q 2) c d).mulVec e) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = _ := by rw [he c d hcd]
  have hh := (upperArrays_fixed_iff q hq (A.mulVec e)).mp hf
  simpa [e, firstBasisVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
