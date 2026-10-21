import SymmetricSubgroupAsymptotics.BinaryPairLargeProductLowerLayer
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension
import SymmetricSubgroupAsymptotics.BinaryPairNaturalHeadDoubleTop

/-! A wide original head constrains the JOINT dimensions of the original
flip kernel and original point submodule. No split lifts or independent
choices of their two pair layers are introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance wideHeadJointDimensionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

private theorem full_pair_layer_head_le_one (i : Fin w)
    (A : Subrepresentation E.coordinateTopAction) (hA : A.toSubmodule = ⊤) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 1 := by
  letI wideHeadJointDimension_topTransitive : MulAction.IsPretransitive E.top.range (Fin w) :=
    E.top_pretransitive
  let lift : (Fin w → ZMod 2) →ₗ[ZMod 2] A.toSubmodule := {
    toFun f := ⟨f, by rw [hA]; exact Submodule.mem_top⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let q := (Representation.Coinvariants.mk A.toRepresentation).comp lift
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨m, hm⟩ := Representation.Coinvariants.mk_surjective A.toRepresentation a
    exact ⟨m.val, hm⟩
  apply PermutationBinaryFourSection.trivial_quotient_finrank_le_one (G := E.top.range) i q hq
  intro g f
  change Representation.Coinvariants.mk A.toRepresentation
    (A.toRepresentation g (lift f)) = Representation.Coinvariants.mk A.toRepresentation (lift f)
  exact Representation.Coinvariants.mk_self_apply _ _ _

theorem wide_natural_head_kernel_add_upper_dimension_le (hU : IsPGroup 2 U)
    (i : Fin w) (c : ℕ)
    (hcap : ∀ A : Subrepresentation E.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : c < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) E.kernelSpace +
      Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule ≤ w := by
  have hS := hcap (E.descendPairLayer (E.pairSumModuleLayer W))
  rw [← E.descendPairLayer_head] at hS
  by_contra hbad
  have hh := E.pairModuleHead_le_upperHead_of_dimension_sum hU i W (by omega)
  omega

theorem wide_natural_head_joint_dimension_le (hU : IsPGroup 2 U)
    (i : Fin w) (c : ℕ)
    (hcap : ∀ A : Subrepresentation E.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : c < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule ≤ 2 * w := by
  have hs := E.wide_natural_head_kernel_add_upper_dimension_le hU i c hcap W hwide
  have hl := Submodule.finrank_le (E.pairConstantModuleLayer W).toSubmodule
  have hw : Module.finrank (ZMod 2) (Fin w → ZMod 2) = w := by simp
  rw [hw] at hl
  have hd := E.pairModuleLayers_finrank W
  omega

theorem wide_natural_head_lower_layer_ne_top (i : Fin w) (c : ℕ)
    (hcap : ∀ A : Subrepresentation E.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : c + 1 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (E.pairConstantModuleLayer W).toSubmodule ≠ ⊤ := by
  intro hfull
  let L := E.pairConstantModuleLayer W
  let S := E.pairSumModuleLayer W
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
  have hL := E.full_pair_layer_head_le_one i (E.descendPairLayer L) hfull
  have hS := hcap (E.descendPairLayer S)
  rw [← E.descendPairLayer_head L] at hL
  rw [← E.descendPairLayer_head S] at hS
  omega

theorem very_wide_natural_head_joint_dimension_lt (hU : IsPGroup 2 U)
    (i : Fin w) (c : ℕ)
    (hcap : ∀ A : Subrepresentation E.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : c + 1 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule < 2 * w := by
  have hs := E.wide_natural_head_kernel_add_upper_dimension_le hU i c hcap W (by omega)
  have hl := Submodule.finrank_lt (E.wide_natural_head_lower_layer_ne_top i c hcap W hwide)
  have hw : Module.finrank (ZMod 2) (Fin w → ZMod 2) = w := by simp
  rw [hw] at hl
  have hd := E.pairModuleLayers_finrank W
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
