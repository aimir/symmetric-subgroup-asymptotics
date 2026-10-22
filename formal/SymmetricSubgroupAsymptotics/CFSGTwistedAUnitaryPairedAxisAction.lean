import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedRootJoin
import SymmetricSubgroupAsymptotics.CFSGTwistedAEndpointBlock

/-! Exact actions of the literal endpoint-paired roots on the first
two coordinate axes. The remote endpoint contributes zero on these axes;
all field and characteristic choices remain unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

theorem disjoint_root_first_axis {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (p q r t : I) (hpq : p ≠ q) (hpt : p ≠ t) (a c b : K) :
    ((1 : Matrix I I K) + Matrix.single p q a + Matrix.single r t c) *ᵥ
      Pi.single p b = Pi.single p b := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_single]
  simp [Pi.single_apply, Ne.symm hpq, Ne.symm hpt]

theorem disjoint_root_second_axis {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (p q r t : I) (hqt : q ≠ t) (a c b : K) :
    ((1 : Matrix I I K) + Matrix.single p q a + Matrix.single r t c) *ᵥ
      Pi.single q b = Pi.single q b + Pi.single p (a * b) := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_single]
  simp [Pi.single_apply, Ne.symm hqt]

theorem endpointPair_axis_action (q : CFSG.PrimePower) (s : ℕ)
    (neg : Bool) (a b : q.Extension 2) (i : Fin 2) :
    ((endpointNaturalFixedPair q s neg a).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
      Pi.single (CFSGTwistedAFirstBlock.head s i) b =
      if neg then
        (if i = 0 then Pi.single (CFSGTwistedAFirstBlock.head s 0) b +
          Pi.single (CFSGTwistedAFirstBlock.head s 1) (a * b)
        else Pi.single (CFSGTwistedAFirstBlock.head s 1) b)
      else
        (if i = 0 then Pi.single (CFSGTwistedAFirstBlock.head s 0) b
        else Pi.single (CFSGTwistedAFirstBlock.head s 1) b +
          Pi.single (CFSGTwistedAFirstBlock.head s 0) (a * b)) := by
  have h0 : (endpointNode s).castSucc = CFSGTwistedAFirstBlock.head s 0 := Fin.ext rfl
  have h1 : (endpointNode s).succ = CFSGTwistedAFirstBlock.head s 1 := Fin.ext rfl
  have hd : CFSGTwistedAFirstBlock.head s (0 : Fin 2) ≠
      CFSGTwistedAFirstBlock.head s 1 := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    change (0 : ℕ) = 1 at hv
    omega
  have hc (j : Fin 2) : CFSGTwistedAFirstBlock.head s j ≠ (endpointNode s).rev.castSucc := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    have hj := j.isLt
    simp only [CFSGTwistedAFirstBlock.head, Fin.val_mk, endpointNode,
      Fin.val_castSucc, Fin.val_rev] at hv
    omega
  have ht (j : Fin 2) : CFSGTwistedAFirstBlock.head s j ≠ (endpointNode s).rev.succ := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    have hj := j.isLt
    simp only [CFSGTwistedAFirstBlock.head, Fin.val_mk, endpointNode,
      Fin.val_succ, Fin.val_rev] at hv
    omega
  rw [endpointNaturalFixedPair_matrix]
  cases neg
  · simp only [Bool.false_eq_true, if_false, rootMatrix, positive,
      Matrix.smul_single, smul_eq_mul, mul_one, h0, h1]
    fin_cases i
    · simpa only [if_true] using disjoint_root_first_axis
        (CFSGTwistedAFirstBlock.head s 0) (CFSGTwistedAFirstBlock.head s 1)
        (endpointNode s).rev.castSucc (endpointNode s).rev.succ hd (ht 0)
        a (definingFieldAutomorphism q 2 a) b
    · simpa using disjoint_root_second_axis
        (CFSGTwistedAFirstBlock.head s 0) (CFSGTwistedAFirstBlock.head s 1)
        (endpointNode s).rev.castSucc (endpointNode s).rev.succ (ht 1)
        a (definingFieldAutomorphism q 2 a) b
  · simp only [if_true, rootMatrix, negative, positive, Matrix.transpose_single,
      Matrix.smul_single, smul_eq_mul, mul_one, h0, h1]
    fin_cases i
    · simpa only [if_true] using disjoint_root_second_axis
        (CFSGTwistedAFirstBlock.head s 1) (CFSGTwistedAFirstBlock.head s 0)
        (endpointNode s).rev.succ (endpointNode s).rev.castSucc (hc 0)
        a (definingFieldAutomorphism q 2 a) b
    · simpa using disjoint_root_first_axis
        (CFSGTwistedAFirstBlock.head s 1) (CFSGTwistedAFirstBlock.head s 0)
        (endpointNode s).rev.succ (endpointNode s).rev.castSucc (Ne.symm hd) (hc 1)
        a (definingFieldAutomorphism q 2 a) b

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
