import SymmetricSubgroupAsymptotics.BinaryPairWideHeadJointDimension

/-! The actual upper layer must carry the head which the bounded lower
layer cannot supply. Its dimension leaves correspondingly less room for
the SAME original inner flip kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem kernel_dimension_add_wide_head_le (hU : IsPGroup 2 U) (i : Fin w) (c : ℕ)
    (hcap : ∀ A : Subrepresentation E.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : c < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) E.kernelSpace +
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ w + c := by
  let S := E.pairSumModuleLayer W
  let L := E.pairConstantModuleLayer W
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
  have hL := hcap (E.descendPairLayer L)
  rw [← E.descendPairLayer_head L] at hL
  have hS := LinearMap.finrank_le_finrank_of_surjective
    (Representation.Coinvariants.mk_surjective S.toRepresentation)
  change Module.finrank (ZMod 2) S.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) S.toSubmodule at hS
  have hd := E.wide_natural_head_kernel_add_upper_dimension_le hU i c hcap W hwide
  change Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) S.toSubmodule ≤ w at hd
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
