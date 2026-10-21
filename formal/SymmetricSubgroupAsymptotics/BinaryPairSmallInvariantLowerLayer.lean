import SymmetricSubgroupAsymptotics.PGroupPermutationPointwiseAnnihilator
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerTopTransport
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! A small invariant subspace of the SAME original point module lies
in its literal pair-constant layer. A nonzero upper image contains one;
actual kernel shears then place the entire actual kernel in the lower
layer, which costs one dimension more than that kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance smallInvariantLowerLayerPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem small_invariant_subrepresentation_le_pairSum_kernel
    (hU : IsPGroup 2 U) (i : Fin w)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hdim : Module.finrank (ZMod 2) W.toSubmodule ≤
      Module.finrank (ZMod 2) F.kernelSpace) : W.toSubmodule ≤ F.pairSum.ker := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  let S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)) :=
    F.descendPairLayer (F.pairSumModuleLayer W)
  by_contra hnot
  have hne : S.toSubmodule ≠ ⊥ := by
    intro he
    apply hnot
    intro v hv
    have hm : F.pairSum v ∈ S.toSubmodule := ⟨v,hv,rfl⟩
    rw [he] at hm
    exact hm
  have hone := pGroup_permutation_subrepresentation_contains_one (F.top_isPGroup hU) i S hne
  have hJ : F.kernelSpace ≤ (F.pairConstantModuleLayer W).toSubmodule := by
    intro a ha
    have hm := F.actual_kernel_pairSum_product_le_constantLayer W
      (Submodule.subset_span
        (show a ∈ {v | ∃ x ∈ F.kernelSpace,∃ y ∈ (F.pairSumModuleLayer W).toSubmodule,
            v=x*y} from ⟨a,ha,fun _ => 1,hone,by ext j;exact (mul_one (a j)).symm⟩))
    exact hm
  have hlow := Submodule.finrank_mono hJ
  have hupp : 1 ≤ Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule :=
    Submodule.one_le_finrank_iff.mpr hne
  have hsum := F.pairModuleLayers_finrank W
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
