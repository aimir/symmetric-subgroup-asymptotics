import SymmetricSubgroupAsymptotics.BinaryPairAxisRadicalSpace
import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalCarrySpaces

/-! Large original intersection heads select the same literal natural
module and radical rows as the checked degree-eight registries. Every
space here is an axis of the original normal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) (hU : IsPGroup 2 U)
  (B : Subgroup U) [B.Normal] (hB : B ≤ F.top.ker)

include hU hB

theorem regular_large_axis_models
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hlarge : 2 < MarkedC4.normalGen B) :
    (F.ambientAxis B = BinaryRegularEightSquareCarry.K45 ∧
      F.ambientAxis (primeRelativeRadical 2 B) = BinaryRegularEightSquareCarry.R45) ∨
    (F.ambientAxis B = BinaryRegularEightSquareCarry.K46 ∧
      F.ambientAxis (primeRelativeRadical 2 B) = BinaryRegularEightSquareCarry.R46) := by
  let W := F.literalTopAxis BinaryRegularEightNaturalRegistry.H hH B
  have hh : MarkedC4.normalGen B =
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    (F.axis_normalGen_eq_coinvariants B hB hU).trans
      (F.literalTopAxis_head BinaryRegularEightNaturalRegistry.H hH B).symm
  have hhead : 2 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by omega
  have hs : W.toSubmodule = F.ambientAxis B :=
    F.literalTopAxis_space BinaryRegularEightNaturalRegistry.H hH B
  have hr : F.ambientAxis (primeRelativeRadical 2 B) =
      (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype :=
    (F.ambientAxis_radical_eq_coinvariants_radical B hB).trans
      (F.literalTopAxis_radical BinaryRegularEightNaturalRegistry.H hH B).symm
  rcases BinaryRegularEightNaturalRegistry.head_gt_two_states W hhead with h45 | h46
  · left
    constructor
    · exact hs.symm.trans ((congrArg Subrepresentation.toSubmodule h45).trans
        BinaryRegularEightNaturalRegistry.kernel45_space)
    · rw [h45] at hr
      exact hr.trans ((BinaryRegularEightNaturalRegistry.coinvariantsKer_map_eq_radical 45).trans
        BinaryRegularEightNaturalRegistry.radical45_space)
  · right
    constructor
    · exact hs.symm.trans ((congrArg Subrepresentation.toSubmodule h46).trans
        BinaryRegularEightNaturalRegistry.kernel46_space)
    · rw [h46] at hr
      exact hr.trans ((BinaryRegularEightNaturalRegistry.coinvariantsKer_map_eq_radical 46).trans
        BinaryRegularEightNaturalRegistry.radical46_space)

theorem heisenberg_large_axis_models
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hlarge : 1 < MarkedC4.normalGen B) :
    (F.ambientAxis B = BinaryHeisenbergEightSquareCarry.K12 ∧
      F.ambientAxis (primeRelativeRadical 2 B) = BinaryHeisenbergEightSquareCarry.R12) ∨
    (F.ambientAxis B = BinaryHeisenbergEightSquareCarry.K13 ∧
      F.ambientAxis (primeRelativeRadical 2 B) = BinaryHeisenbergEightSquareCarry.R13) ∨
    (F.ambientAxis B = BinaryHeisenbergEightSquareCarry.K14 ∧
      F.ambientAxis (primeRelativeRadical 2 B) = BinaryHeisenbergEightSquareCarry.R14) := by
  let W := F.literalTopAxis BinaryHeisenbergEightNaturalHeads.H hH B
  have hh : MarkedC4.normalGen B =
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    (F.axis_normalGen_eq_coinvariants B hB hU).trans
      (F.literalTopAxis_head BinaryHeisenbergEightNaturalHeads.H hH B).symm
  have hhead : 1 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by omega
  have hs : W.toSubmodule = F.ambientAxis B :=
    F.literalTopAxis_space BinaryHeisenbergEightNaturalHeads.H hH B
  have hr : F.ambientAxis (primeRelativeRadical 2 B) =
      (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype :=
    (F.ambientAxis_radical_eq_coinvariants_radical B hB).trans
      (F.literalTopAxis_radical BinaryHeisenbergEightNaturalHeads.H hH B).symm
  rcases BinaryHeisenbergEightNaturalHeads.head_gt_one_states W hhead with h12 | h13 | h14
  · left
    constructor
    · exact hs.symm.trans ((congrArg Subrepresentation.toSubmodule h12).trans
        BinaryHeisenbergEightNaturalHeads.kernel12_space)
    · rw [h12] at hr
      exact hr.trans ((BinaryHeisenbergEightNaturalHeads.coinvariantsKer_map_eq_radical 12).trans
        BinaryHeisenbergEightNaturalHeads.radical12_space)
  · right; left
    constructor
    · exact hs.symm.trans ((congrArg Subrepresentation.toSubmodule h13).trans
        BinaryHeisenbergEightNaturalHeads.kernel13_space)
    · rw [h13] at hr
      exact hr.trans ((BinaryHeisenbergEightNaturalHeads.coinvariantsKer_map_eq_radical 13).trans
        BinaryHeisenbergEightNaturalHeads.radical13_space)
  · right; right
    constructor
    · exact hs.symm.trans ((congrArg Subrepresentation.toSubmodule h14).trans
        BinaryHeisenbergEightNaturalHeads.kernel14_space)
    · rw [h14] at hr
      exact hr.trans ((BinaryHeisenbergEightNaturalHeads.coinvariantsKer_map_eq_radical 14).trans
        BinaryHeisenbergEightNaturalHeads.radical14_space)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
