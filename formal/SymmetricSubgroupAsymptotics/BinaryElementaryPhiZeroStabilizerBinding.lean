import SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizerData
import SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroIntrinsicRadical

/-! The selected scalar-count packet uses the exact original phi-zero
state and intrinsic radical. Only their original ordered basis columns
are compared; no module or group cases are added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroStabilizerBinding
open BinarySplitElementary16PhiZeroStabilizer
private theorem state_basis : ∀ j : Fin 11,
    state.inclusion (Pi.single j 1) =
      (BinaryElementary16GraphHeadRigidity.stateChart 0).inclusion (Pi.single j 1) := by decide +kernel
private theorem radical_basis : ∀ j : Fin 5,
    radical.inclusion (Pi.single j 1) =
      BinaryElementaryPhiZeroIntrinsicRadical.radical.inclusion (Pi.single j 1) := by decide +kernel

theorem state_eq_original_graph : state.space = (BinaryElementary16GraphHeadRigidity.stateChart 0).space := by
  have he : state.inclusion = (BinaryElementary16GraphHeadRigidity.stateChart 0).inclusion := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 11 → ZMod 2) = c • Pi.single i 1 := by
      funext j;simp [Pi.single_apply,mul_ite]
    simp only [hs,map_smul,state_basis]
  change state.inclusion.range = (BinaryElementary16GraphHeadRigidity.stateChart 0).inclusion.range
  rw [he]

theorem radical_eq_intrinsic : radical.space = BinaryElementaryPhiZeroIntrinsicRadical.radical.space := by
  have he : radical.inclusion = BinaryElementaryPhiZeroIntrinsicRadical.radical.inclusion := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 5 → ZMod 2) = c • Pi.single i 1 := by
      funext j;simp [Pi.single_apply,mul_ite]
    simp only [hs,map_smul,radical_basis]
  change radical.inclusion.range = BinaryElementaryPhiZeroIntrinsicRadical.radical.inclusion.range
  rw [he]

end SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroStabilizerBinding
