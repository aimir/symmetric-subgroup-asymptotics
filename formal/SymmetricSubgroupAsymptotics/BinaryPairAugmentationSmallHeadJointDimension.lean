import SymmetricSubgroupAsymptotics.BinaryPairWideHeadJointDimension

/-! If the actual top augmentation has head at most one, a head-four
original submodule cannot have a hyperplane as its lower pair layer.
The resulting strict JOINT dimension bound retains the original kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance augmentationSmallHeadJointPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem head_four_joint_dimension_add_two_le (hU : IsPGroup 2 U) (i : Fin w)
    (hcap : ∀ A : Subrepresentation E.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2)
    (haug : ∀ A : Subrepresentation E.coordinateTopAction,
      A.toSubmodule = PermutationAugmentation.space (ZMod 2) (Fin w) →
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 1)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule + 2 ≤ 2 * w := by
  letI augmentationSmallHeadJoint_topTransitive : MulAction.IsPretransitive E.top.range (Fin w) :=
    E.top_pretransitive
  let S := E.pairSumModuleLayer W
  let L := E.pairConstantModuleLayer W
  have hS := hcap (E.descendPairLayer S)
  rw [← E.descendPairLayer_head S] at hS
  have hk : Representation.Coinvariants.ker L.toRepresentation ≤
      ((Representation.Coinvariants.mk W.toRepresentation).comp
        (E.pairConstantLayerInclusion W).toLinearMap).ker :=
    le_trans le_sup_right (E.pairLayerProductDenominator_le_head_kernel W)
  have hb := RepresentationCoinvariantExactDenominator.finrank_coinvariants_le_quotient_add
    (E.pairConstantLayerInclusion W) (E.pairSumLayerProjection W)
    (E.pairSumLayerProjection_surjective W) (E.pairModuleLayers_exact W)
    (Representation.Coinvariants.ker L.toRepresentation) hk
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) L.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants at hb
  have hLwide : 2 ≤ Module.finrank (ZMod 2) L.toRepresentation.Coinvariants := by omega
  have hproper := E.wide_natural_head_lower_layer_ne_top i 2 hcap W (by omega)
  have hle := pGroup_permutation_proper_subrepresentation_le_augmentation
    (E.top_isPGroup hU) i (E.descendPairLayer L) hproper
  have haugdim := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) i
  simp only [Nat.card_fin] at haugdim
  have hLle := Submodule.finrank_mono hle
  have hLdim : Module.finrank (ZMod 2) L.toSubmodule + 2 ≤ w := by
    by_contra hbad
    have heq : (E.descendPairLayer L).toSubmodule =
        PermutationAugmentation.space (ZMod 2) (Fin w) :=
      Submodule.eq_of_le_of_finrank_eq hle (by
        change Module.finrank (ZMod 2) L.toSubmodule =
          Module.finrank (ZMod 2) (PermutationAugmentation.space (ZMod 2) (Fin w))
        change Module.finrank (ZMod 2) L.toSubmodule ≤
          Module.finrank (ZMod 2) (PermutationAugmentation.space (ZMod 2) (Fin w)) at hLle
        omega)
    have hh := haug (E.descendPairLayer L) heq
    rw [← E.descendPairLayer_head L] at hh
    omega
  have hs := E.wide_natural_head_kernel_add_upper_dimension_le hU i 2 hcap W (by omega)
  change Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) S.toSubmodule ≤ w at hs
  have hd := E.pairModuleLayers_finrank W
  change Module.finrank (ZMod 2) W.toSubmodule =
    Module.finrank (ZMod 2) S.toSubmodule + Module.finrank (ZMod 2) L.toSubmodule at hd
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
