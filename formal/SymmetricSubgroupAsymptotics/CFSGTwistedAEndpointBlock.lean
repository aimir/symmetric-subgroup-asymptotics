import SymmetricSubgroupAsymptotics.CFSGTwistedAEndpointFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedAFirstBlock
import SymmetricSubgroupAsymptotics.CFSGTwistedASLTwoDerivedWitness

/-! Exact first-block coordinates of the literal endpoint natural roots.
The tail factor contributes the identity block. Both the original unit
and its inverse preserve the block, so restriction is an actual hom. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSGTwistedAFirstBlock CFSGTypeASLTwoWeyl CFSGTypeAElementaryMatrices
variable (K : Type) [Field K] (s : ℕ)

theorem rowsClosed_single_add (a b : Fin (s + 4)) (t : K)
    (hab : a.val < 2 → b.val < 2) :
    RowsClosed K s (1 + t • Matrix.single a b (1 : K)) := by
  intro i k hk
  have hne : head s i ≠ k := by
    intro h
    have hh := congrArg (fun j : Fin (s + 4) => j.val) h
    have hi := i.isLt
    change i.val = k.val at hh
    omega
  have hs : ¬ (head s i = a ∧ k = b) := by
    rintro ⟨hi, hb⟩
    have ha : a.val < 2 := by
      rw [← hi]
      exact i.isLt
    have hb' := hab ha
    rw [← hb] at hb'
    omega
  have hs' : ¬ (a = head s i ∧ b = k) := fun h => hs ⟨h.1.symm, h.2.symm⟩
  simp only [Matrix.add_apply, Matrix.one_apply, if_neg hne, Matrix.smul_apply,
    Matrix.single_apply, if_neg hs', smul_zero, add_zero]

theorem naturalRoot_mem_rowUnits (neg : Bool) (i : Fin (s + 3))
    (hi : i.val + 1 < 2 ∨ 2 ≤ i.val) (t : K) :
    naturalRootUnit K (s + 3) neg i t ∈ rowUnits K s := by
  have hp : i.castSucc.val < 2 → i.succ.val < 2 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hn : i.succ.val < 2 → i.castSucc.val < 2 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  cases neg
  · constructor
    · exact rowsClosed_single_add K s i.castSucc i.succ t hp
    · change RowsClosed K s (1 - t • positive K (s + 3) i)
      simpa only [positive, sub_eq_add_neg, neg_smul] using
        rowsClosed_single_add K s i.castSucc i.succ (-t) hp
  · constructor
    · change RowsClosed K s (1 + t • negative K (s + 3) i)
      simpa only [negative, positive, Matrix.transpose_single] using
        rowsClosed_single_add K s i.succ i.castSucc t hn
    · change RowsClosed K s (1 - t • negative K (s + 3) i)
      simpa only [negative, positive, Matrix.transpose_single, sub_eq_add_neg, neg_smul] using
        rowsClosed_single_add K s i.succ i.castSucc (-t) hn

def endpointRootRowUnit (neg : Bool) (tail : Bool) (t : K) : rowUnits K s :=
  ⟨naturalRootUnit K (s + 3) neg
      (if tail then (endpointNode s).rev else endpointNode s) t,
    naturalRoot_mem_rowUnits K s neg _ (by
      cases tail
      · change (0 : ℕ) + 1 < 2 ∨ 2 ≤ 0
        exact Or.inl (by decide)
      · change (s + 3 - (0 + 1)) + 1 < 2 ∨ 2 ≤ s + 3 - (0 + 1)
        exact Or.inr (by omega)) t⟩

theorem block_endpoint_first (neg : Bool) (t : K) :
    (blockHom K s (endpointRootRowUnit K s neg false t) :
      Matrix (Fin 2) (Fin 2) K) =
        (Matrix.SpecialLinearGroup.toGL (if neg then lower t else upper t) :
          Matrix (Fin 2) (Fin 2) K) := by
  cases neg <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [blockHom, blockUnit, block, head, endpointRootRowUnit, naturalRootUnit,
      rootMatrix, negative, positive, endpointNode, lower, upper,
      Matrix.transvection, elementary_coe]

theorem block_single_of_tail_row (a b : Fin (s + 4)) (t : K) (ha : 2 ≤ a.val) :
    block K s (Matrix.single a b t) = 0 := by
  ext i j
  have hne : head s i ≠ a := by
    intro h
    have hv := congrArg (fun k : Fin (s + 4) => k.val) h
    have hi := i.isLt
    change i.val = a.val at hv
    omega
  have hs : ¬ (a = head s i ∧ b = head s j) := fun h => hne h.1.symm
  simp only [block, Matrix.submatrix_apply, Matrix.single_apply, if_neg hs, Matrix.zero_apply]

theorem block_endpoint_tail (neg : Bool) (t : K) :
    (blockHom K s (endpointRootRowUnit K s neg true t) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
  have hc : 2 ≤ ((endpointNode s).rev.castSucc).val := by
    simp only [Fin.val_castSucc, endpointNode, Fin.val_rev]
    omega
  have hs : 2 ≤ ((endpointNode s).rev.succ).val := by
    simp only [Fin.val_succ, endpointNode, Fin.val_rev]
    omega
  cases neg
  · change block K s (1 + t • positive K (s + 3) (endpointNode s).rev) = 1
    simp only [positive, block, Matrix.submatrix_add, Matrix.submatrix_smul]
    change block K s (1 : BigMat K s) +
      t • block K s (Matrix.single (endpointNode s).rev.castSucc (endpointNode s).rev.succ 1) = 1
    rw [block_one, block_single_of_tail_row K s _ _ _ hc, smul_zero, add_zero]
  · change block K s (1 + t • negative K (s + 3) (endpointNode s).rev) = 1
    simp only [negative, positive, Matrix.transpose_single, block,
      Matrix.submatrix_add, Matrix.submatrix_smul]
    change block K s (1 : BigMat K s) +
      t • block K s (Matrix.single (endpointNode s).rev.succ (endpointNode s).rev.castSucc 1) = 1
    rw [block_one, block_single_of_tail_row K s _ _ _ hs, smul_zero, add_zero]

def pairedEndpointRowUnit (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    rowUnits (q.Extension 2) s :=
  endpointRootRowUnit (q.Extension 2) s neg false t *
    endpointRootRowUnit (q.Extension 2) s neg true (t ^ q.order)

theorem pairedEndpointRowUnit_block (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    blockHom (q.Extension 2) s (pairedEndpointRowUnit s q neg t) =
      Matrix.SpecialLinearGroup.toGL (if neg then lower t else upper t) := by
  apply Units.ext
  change (blockHom (q.Extension 2) s
      (endpointRootRowUnit (q.Extension 2) s neg false t *
        endpointRootRowUnit (q.Extension 2) s neg true (t ^ q.order)) :
          Matrix (Fin 2) (Fin 2) (q.Extension 2)) = _
  rw [map_mul, Units.val_mul, block_endpoint_first, block_endpoint_tail, mul_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
