import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! The pinned D-fork involution is a genuine Cartan-preserving permutation
in every rank, including the degenerate small-rank definitions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram

theorem dTwist_involutive (n : ℕ) : Function.Involutive (@CFSG.Models.dTwist n) := by
  intro i
  by_cases hn : 2 ≤ n
  · simp only [CFSG.Models.dTwist, dif_pos hn]
    split_ifs <;> apply Fin.ext <;> simp_all
  · simp only [CFSG.Models.dTwist, dif_neg hn]

def dPermutation (n : ℕ) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (@CFSG.Models.dTwist n) (dTwist_involutive n)

@[simp] theorem dPermutation_apply (n : ℕ) (i : Fin n) :
    dPermutation n i = CFSG.Models.dTwist i := rfl

private theorem dTwist_chain (n : ℕ) (i j : Fin n) :
    ((CFSG.Models.dTwist i).val + 1 = (CFSG.Models.dTwist j).val ∧
      (CFSG.Models.dTwist j).val + 2 < n) ↔
      (i.val + 1 = j.val ∧ j.val + 2 < n) := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases hn : 2 ≤ n
  · simp only [CFSG.Models.dTwist, dif_pos hn]
    split_ifs <;> simp_all
    all_goals omega
  · simp only [CFSG.Models.dTwist, dif_neg hn]

private theorem dTwist_fork (n : ℕ) (i : Fin n) :
    (CFSG.Models.dTwist i).val + 3 = n ↔ i.val + 3 = n := by
  have hi := i.isLt
  by_cases hn : 2 ≤ n
  · simp only [CFSG.Models.dTwist, dif_pos hn]
    split_ifs <;> simp_all
    all_goals omega
  · simp only [CFSG.Models.dTwist, dif_neg hn]

private theorem dTwist_terminal (n : ℕ) (i : Fin n) :
    ((CFSG.Models.dTwist i).val + 2 = n ∨ (CFSG.Models.dTwist i).val + 1 = n) ↔
      (i.val + 2 = n ∨ i.val + 1 = n) := by
  have hi := i.isLt
  by_cases hn : 2 ≤ n
  · simp only [CFSG.Models.dTwist, dif_pos hn]
    split_ifs <;> simp_all
    all_goals omega
  · simp only [CFSG.Models.dTwist, dif_neg hn]

theorem d_preserves (n : ℕ) (i j : Fin n) :
    CartanMatrix.D n (dPermutation n i) (dPermutation n j) = CartanMatrix.D n i j := by
  have hdiag : CFSG.Models.dTwist i = CFSG.Models.dTwist j ↔ i = j :=
    (dTwist_involutive n).injective.eq_iff
  change CartanMatrix.D n (CFSG.Models.dTwist i) (CFSG.Models.dTwist j) = _
  simp only [CartanMatrix.D, Matrix.of_apply, hdiag, dTwist_chain,
    dTwist_fork, dTwist_terminal]

def dDiagramAutomorphism (n : ℕ) (K : Type) [Field K] :
    MulAut (CFSG.Models.Chevalley.Model (CartanMatrix.D n) K) :=
  modelAutomorphism (CartanMatrix.D n) K (dPermutation n) (d_preserves n)

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
