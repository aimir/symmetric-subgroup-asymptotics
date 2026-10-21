import SymmetricSubgroupAsymptotics.CFSGSerreDiagramTwistGraph
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases

/-! The ordinary diagram permutations in the pinned models preserve their
literal Cartan matrices. Exceptional long--short isogenies are not ordinary
Cartan-preserving diagram actions and are not included here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram

theorem typeA_reverse_preserves (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n (Fin.revPerm i) (Fin.revPerm j) = CartanMatrix.A n i j := by
  have hi := i.isLt
  have hj := j.isLt
  have hrev : i.rev = j.rev ↔ i = j := Fin.rev_injective.eq_iff
  have hadj : i.rev.val + 1 = j.rev.val ∨ j.rev.val + 1 = i.rev.val ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
    simp only [Fin.val_rev]
    omega
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.revPerm_apply, hrev, hadj]

def e6Permutation : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective CFSG.Models.e6Twist (by decide)

@[simp] theorem e6Permutation_apply (i : Fin 6) :
    e6Permutation i = CFSG.Models.e6Twist i := rfl

theorem e6_preserves (i j : Fin 6) :
    CartanMatrix.E₆ (e6Permutation i) (e6Permutation j) = CartanMatrix.E₆ i j := by
  fin_cases i <;> fin_cases j <;> decide

def trialityPermutation : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective CFSG.Models.triality (by decide)

@[simp] theorem trialityPermutation_apply (i : Fin 4) :
    trialityPermutation i = CFSG.Models.triality i := rfl

theorem triality_preserves (i j : Fin 4) :
    CartanMatrix.D 4 (trialityPermutation i) (trialityPermutation j) =
      CartanMatrix.D 4 i j := by
  fin_cases i <;> fin_cases j <;> decide

def typeADiagramAutomorphism (n : ℕ) (K : Type) [Field K] :
    MulAut (CFSG.Models.Chevalley.Model (CartanMatrix.A n) K) :=
  modelAutomorphism (CartanMatrix.A n) K Fin.revPerm (typeA_reverse_preserves n)

def e6DiagramAutomorphism (K : Type) [Field K] :
    MulAut (CFSG.Models.Chevalley.Model CartanMatrix.E₆ K) :=
  modelAutomorphism CartanMatrix.E₆ K e6Permutation e6_preserves

def trialityDiagramAutomorphism (K : Type) [Field K] :
    MulAut (CFSG.Models.Chevalley.Model (CartanMatrix.D 4) K) :=
  modelAutomorphism (CartanMatrix.D 4) K trialityPermutation triality_preserves

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
