import SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizerCountData
import SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroIntrinsicRadical

/-! The selected scalar-count packet uses the exact original phi-zero
state and intrinsic radical. Only their original ordered basis columns
are compared; no module or group cases are added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroStabilizerBinding
open BinarySplitHeisenberg14PhiZeroStabilizer
private theorem state_basis : ∀ j : Fin 10,
    state.inclusion (Pi.single j 1) =
      (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).inclusion (Pi.single j 1) := by decide +kernel
private theorem radical_basis : ∀ j : Fin 6,
    radical.inclusion (Pi.single j 1) =
      BinaryHeisenbergPhiZeroIntrinsicRadical.radical.inclusion (Pi.single j 1) := by decide +kernel

theorem state_eq_original_graph : state.space = (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space := by
  have he : state.inclusion = (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).inclusion := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 10 → ZMod 2) = c • Pi.single i 1 := by
      funext j;simp [Pi.single_apply,mul_ite]
    simp only [hs,map_smul,state_basis]
  change state.inclusion.range = (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).inclusion.range
  rw [he]

theorem radical_eq_intrinsic : radical.space = BinaryHeisenbergPhiZeroIntrinsicRadical.radical.space := by
  have he : radical.inclusion = BinaryHeisenbergPhiZeroIntrinsicRadical.radical.inclusion := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 6 → ZMod 2) = c • Pi.single i 1 := by
      funext j;simp [Pi.single_apply,mul_ite]
    simp only [hs,map_smul,radical_basis]
  change radical.inclusion.range = BinaryHeisenbergPhiZeroIntrinsicRadical.radical.inclusion.range
  rw [he]

end SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroStabilizerBinding
