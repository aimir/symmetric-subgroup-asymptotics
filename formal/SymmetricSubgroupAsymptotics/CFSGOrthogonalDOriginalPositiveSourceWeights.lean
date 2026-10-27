import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveProfile
import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights

/-! Weights in the SAME original rational D Serre quotient, before any
source-spanning or faithfulness statement. The literal fork path is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveSourceWeights
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreDividedPowerPaths CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformPositiveProfile
variable (r : ℕ) (hr : 4 ≤ r)

def source : PositiveIndex r → RationalLie (CartanMatrix.D r)
  | .inl i => generator (CartanMatrix.D r) (.H i)
  | .inr j => (root r hr false j).val

def rootWeight (a : Fin r) : RootIndex r → ℚ
  | .inl ij =>
    let start : Fin r := ⟨ij.val.2.val-1,by have h:=ij.val.2.isLt;omega⟩
    pathWeight (CartanMatrix.D r) a start (steps r (descend r ij.val.1 start))
  | .inr ij =>
    let last : Fin r := ⟨r-1,by omega⟩
    let previous : Fin r := ⟨r-2,by omega⟩
    pathWeight (CartanMatrix.D r) a last
      (steps r (descend r ij.val.1 previous ++ descend r ij.val.2 last))

def weight (a : Fin r) : PositiveIndex r → ℚ
  | .inl _ => 0
  | .inr j => rootWeight r hr a j

theorem root_weight (a : Fin r) (j : RootIndex r) :
    ⁅coroot (CartanMatrix.D r) false a,(root r hr false j).val⁆ =
      rootWeight r hr a j • (root r hr false j).val := by
  cases j <;>
    simpa only [root,difference,sumRoot,path,Bool.false_eq_true,if_false,one_smul,
      rootWeight] using pathVector_weight (CartanMatrix.D r) false a _ _

theorem source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.D r) false a,source r hr j⁆ =
      weight r hr a j • source r hr j := by
  cases j with
  | inl i =>
    simpa only [source,weight,zero_smul,coroot,Bool.false_eq_true,if_false] using
      coroots_commute (CartanMatrix.D r) false a i
  | inr j => exact root_weight r hr a j

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveSourceWeights
