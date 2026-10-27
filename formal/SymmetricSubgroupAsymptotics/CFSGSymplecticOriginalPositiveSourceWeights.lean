import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalCartanTail
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveProfile

/-! Actual rational weights of the original positive source paths and
integral Cartan tails. This uses only original Serre relations, before
any source spanning or realization injectivity theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveSourceWeights
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreDividedPowerPaths CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticOriginalCartanTail CFSGSymplecticUniformPositiveProfile
variable (r : ℕ)

def source : PositiveIndex r → RationalLie (CartanMatrix.C r).transpose
  | .inl i => (tail r i.val).val
  | .inr j => (root r false j).val

def rootWeight (a : Fin r) : RootIndex r → ℚ
  | .inl ij =>
    let start : Fin r := ⟨ij.val.2.val-1, by have h := ij.property; omega⟩
    pathWeight (CartanMatrix.C r).transpose a start
      (steps r (descend r ij.val.1 start) 1)
  | .inr (.inl i) =>
    let last : Fin r := ⟨r-1, by have h := i.isLt; omega⟩
    pathWeight (CartanMatrix.C r).transpose a last
      (steps r (descend r i last) 2)
  | .inr (.inr ij) =>
    let last : Fin r := ⟨r-1, by have h := ij.val.2.isLt; omega⟩
    pathWeight (CartanMatrix.C r).transpose a last
      (steps r (descend r ij.val.2 last) 2 ++
       steps r (descend r ij.val.1 ij.val.2) 1)

def weight (a : Fin r) : PositiveIndex r → ℚ
  | .inl _ => 0
  | .inr j => rootWeight r a j

theorem root_weight (a : Fin r) (j : RootIndex r) :
    ⁅coroot (CartanMatrix.C r).transpose false a,(root r false j).val⁆ =
      rootWeight r a j • (root r false j).val := by
  rcases j with ij | (i | ij) <;>
    simpa only [root, difference, long, sumRoot, path, Bool.false_eq_true, if_false, one_smul,
      rootWeight] using pathVector_weight (CartanMatrix.C r).transpose false a _ _

theorem tail_weight (a : Fin r) (j : ℕ) :
    ⁅coroot (CartanMatrix.C r).transpose false a,(tail r j).val⁆ = 0 := by
  unfold tail
  simp only [Submodule.coe_sum, lie_sum]
  apply Finset.sum_eq_zero
  intro b hb
  unfold Hnat
  split_ifs with h
  · exact coroots_commute (CartanMatrix.C r).transpose false a ⟨j+b,h⟩
  · simp

theorem source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.C r).transpose false a,source r j⁆ =
      weight r a j • source r j := by
  cases j with
  | inl i => simpa only [source,weight,zero_smul] using tail_weight r a i.val
  | inr j => exact root_weight r a j

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveSourceWeights
