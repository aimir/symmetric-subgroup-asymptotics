import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedRotation
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMonomialEntries

/-! Literal monomial chart of the actual paired Weyl word, with all
nonzero signed row weights retained. The four-coordinate proof is
symbolic over an arbitrary finite index type and coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGMatrixPairRotation CFSGTypeAMonomialMatrices CFSGTwistedANaturalMatrices

def pairPermutation {I : Type*} [DecidableEq I] (p q r t : I) : Equiv.Perm I :=
  (Equiv.swap p q).trans (Equiv.swap r t)

def pairWeights {K I : Type*} [CommRing K] [DecidableEq I] (p r : I) (i : I) : K :=
  if i = p ∨ i = r then -1 else 1

theorem pairWeights_ne_zero {K I : Type*} [Field K] [DecidableEq I] (p r i : I) :
    pairWeights (K := K) p r i ≠ 0 := by
  unfold pairWeights
  split_ifs <;> simp

theorem single_rotation_monomial {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (p q : I) (hpq : p ≠ q) :
    rotation K p q = monomial (Equiv.swap p q) (fun i => if i = p then -1 else 1) := by
  ext i j
  by_cases hip : i = p
  · subst i
    by_cases hpj : p = j <;> by_cases hqj : q = j
    all_goals simp_all [rotation, monomial_apply, Matrix.single_apply, Matrix.one_apply, eq_comm]
  · by_cases hiq : i = q
    · subst i
      by_cases hpj : p = j <;> by_cases hqj : q = j
      all_goals simp_all [rotation, monomial_apply, Matrix.single_apply, Matrix.one_apply]
    · simp [rotation, monomial_apply, Matrix.single_apply, Matrix.one_apply,
        hip, hiq, Ne.symm hip, Ne.symm hiq, Equiv.swap_apply_of_ne_of_ne hip hiq]

theorem monomial_mul_monomial {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma tau : Equiv.Perm I) (d e : I → K) :
    monomial sigma d * monomial tau e =
      monomial (sigma.trans tau) (fun i => d i * e (sigma i)) := by
  have hl (R : Matrix I I K) (i j : I) :
      (monomial sigma d * R) i j = d i * R (sigma i) j := by
    simp [Matrix.mul_apply, monomial_apply, ite_mul]
  ext i j
  rw [hl]
  simp only [monomial_apply, Equiv.trans_apply, mul_ite, mul_zero]
  rfl

theorem double_rotation_monomial {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (p q r t : I) (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t)
    (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) :
    rotation K p q * rotation K r t =
      monomial (pairPermutation p q r t) (pairWeights (K := K) p r) := by
  rw [single_rotation_monomial p q hpq, single_rotation_monomial r t hrt,
    monomial_mul_monomial]
  apply congrArg (monomial (pairPermutation p q r t))
  funext i
  have hs : Equiv.swap p q i = r ↔ i = r := by
    rw [(Equiv.swap p q).apply_eq_iff_eq_symm_apply]
    simp only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (Ne.symm hpr) (Ne.symm hqr)]
  simp only [hs, pairWeights]
  by_cases hip : i = p <;> by_cases hir : i = r
  all_goals simp_all

theorem endpointPairWeyl_monomial (q : CFSG.PrimePower) (s : ℕ) :
    ((endpointPairWeyl q s).val.val : Mat (q.Extension 2) (s + 3)) =
      monomial (pairPermutation (endpointNode s).castSucc (endpointNode s).succ
        (endpointNode s).rev.castSucc (endpointNode s).rev.succ)
        (pairWeights (K := q.Extension 2) (endpointNode s).castSucc (endpointNode s).rev.castSucc) := by
  rw [endpointPairWeyl_matrix]
  apply double_rotation_monomial
  all_goals intro he
  all_goals have hv := congrArg (fun i : Fin (s + 4) => i.val) he
  all_goals simp only [endpointNode, Fin.val_castSucc, Fin.val_succ, Fin.val_rev] at hv
  all_goals omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
