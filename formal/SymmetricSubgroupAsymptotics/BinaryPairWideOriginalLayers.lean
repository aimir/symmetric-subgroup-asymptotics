import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerTopTransport
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel46
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14

/-! The literal layer classifications apply to the layers of the original
module, retaining their actual kernel-product denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem pairModuleHead_le_literalLayers
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
      Module.finrank (ZMod 2)
        (F.literalPairLayer H hH (F.pairSumModuleLayer W)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2)
        ((F.literalPairLayer H hH (F.pairConstantModuleLayer W)).toSubmodule ⧸
          ((binaryCoordinateProductSpan F.kernelSpace
            (F.literalPairLayer H hH (F.pairSumModuleLayer W)).toSubmodule).comap
              (F.literalPairLayer H hH (F.pairConstantModuleLayer W)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker
              (F.literalPairLayer H hH (F.pairConstantModuleLayer W)).toRepresentation)) := by
  subst H
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) (F.descendPairLayer (F.pairSumModuleLayer W)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) ((F.pairConstantModuleLayer W).toSubmodule ⧸
        ((binaryCoordinateProductSpan F.kernelSpace (F.pairSumModuleLayer W).toSubmodule).comap
          (F.pairConstantModuleLayer W).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker
              (F.descendPairLayer (F.pairConstantModuleLayer W)).toRepresentation))
  let S := F.pairSumModuleLayer W
  let L := F.pairConstantModuleLayer W
  have hden := congrArg
    (fun R : Submodule (ZMod 2) L.toSubmodule =>
      (binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔ R)
      (F.descendPairLayer_radical L).symm
  have hquot :
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) =
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation)) :=
    (Submodule.quotEquivOfEq _ _ hden).finrank_eq
  have hhead := F.descendPairLayer_head S
  have hw := F.pairModuleHead_le_product_quotient_add W
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) (L.toSubmodule ⧸
      ((binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔
        Representation.Coinvariants.ker L.toRepresentation)) +
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants at hw
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) (F.descendPairLayer S).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation))
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem regular46_four_le_head_forces_original_layers
    (hH : F.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : F.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    ((F.pairSumModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 23).2.space ∧
      (F.pairConstantModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 45).2.space) ∨
    ((F.pairSumModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 46).2.space ∧
      (F.pairConstantModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 1).2.space) := by
  let S := F.literalPairLayer BinaryRegularEightNaturalRegistry.H hH (F.pairSumModuleLayer W)
  let L := F.literalPairLayer BinaryRegularEightNaturalRegistry.H hH (F.pairConstantModuleLayer W)
  have hp : binaryCoordinateProductSpan (BinaryRegularEightNaturalRegistry.charts 46).2.space
      S.toSubmodule ≤ L.toSubmodule := by
    have hp := F.actual_kernel_pairSum_product_le_constantLayer W
    rw [hK] at hp
    simpa only [S,L,F.literalPairLayer_space] using hp
  have hb := hwide.trans (F.pairModuleHead_le_literalLayers _ hH W)
  rw [hK] at hb
  rcases BinaryPairLayerHead8T3Kernel46.four_le_pair_head_forces_layers S L hp hb with
    ⟨hs,hl⟩ | ⟨hs,hl⟩
  · apply Or.inl
    constructor
    · simpa only [S,F.literalPairLayer_space,BinaryRegularEightNaturalRegistry.states_space] using
        congrArg Subrepresentation.toSubmodule hs
    · simpa only [L,F.literalPairLayer_space,BinaryRegularEightNaturalRegistry.states_space] using
        congrArg Subrepresentation.toSubmodule hl
  · apply Or.inr
    constructor
    · simpa only [S,F.literalPairLayer_space,BinaryRegularEightNaturalRegistry.states_space] using
        congrArg Subrepresentation.toSubmodule hs
    · simpa only [L,F.literalPairLayer_space,BinaryRegularEightNaturalRegistry.states_space] using
        congrArg Subrepresentation.toSubmodule hl

theorem heisenberg14_four_le_head_forces_original_layers
    (hH : F.top.range = BinaryHeisenbergEightNaturalHeads.H)
    (hK : F.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (F.pairSumModuleLayer W).toSubmodule = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space ∧
      (F.pairConstantModuleLayer W).toSubmodule = (BinaryHeisenbergEightNaturalHeads.charts 12).2.space := by
  let S := F.literalPairLayer BinaryHeisenbergEightNaturalHeads.H hH (F.pairSumModuleLayer W)
  let L := F.literalPairLayer BinaryHeisenbergEightNaturalHeads.H hH (F.pairConstantModuleLayer W)
  have hp : binaryCoordinateProductSpan (BinaryHeisenbergEightNaturalHeads.charts 14).2.space
      S.toSubmodule ≤ L.toSubmodule := by
    have hp := F.actual_kernel_pairSum_product_le_constantLayer W
    rw [hK] at hp
    simpa only [S,L,F.literalPairLayer_space] using hp
  have hb := hwide.trans (F.pairModuleHead_le_literalLayers _ hH W)
  rw [hK] at hb
  obtain ⟨hs,hl⟩ := BinaryPairLayerHead8T22Kernel14.four_le_pair_head_forces_layers S L hp hb
  constructor
  · simpa only [S,F.literalPairLayer_space,BinaryHeisenbergEightNaturalHeads.states_space] using
      congrArg Subrepresentation.toSubmodule hs
  · simpa only [L,F.literalPairLayer_space,BinaryHeisenbergEightNaturalHeads.states_space] using
      congrArg Subrepresentation.toSubmodule hl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
