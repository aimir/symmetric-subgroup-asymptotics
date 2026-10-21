import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerTopTransport
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! Two genuine original pair layers cost at most twice the uniform
head bound of the actual top. Arbitrary affine offsets are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem naturalModuleHead_le_twice_actual_top (c : ℕ)
    (hcap : ∀ A : Subrepresentation F.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ c + c := by
  let L := F.pairConstantModuleLayer W
  let S := F.pairSumModuleLayer W
  have hk : Representation.Coinvariants.ker L.toRepresentation ≤
      ((Representation.Coinvariants.mk W.toRepresentation).comp
        (F.pairConstantLayerInclusion W).toLinearMap).ker := by
    apply le_trans _ (F.pairLayerProductDenominator_le_head_kernel W)
    exact le_sup_right
  have hb := RepresentationCoinvariantExactDenominator.finrank_coinvariants_le_quotient_add
    (F.pairConstantLayerInclusion W) (F.pairSumLayerProjection W)
    (F.pairSumLayerProjection_surjective W) (F.pairModuleLayers_exact W)
    (Representation.Coinvariants.ker L.toRepresentation) hk
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) L.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants at hb
  have hL := hcap (F.descendPairLayer L)
  have hS := hcap (F.descendPairLayer S)
  rw [← F.descendPairLayer_head L] at hL
  rw [← F.descendPairLayer_head S] at hS
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
