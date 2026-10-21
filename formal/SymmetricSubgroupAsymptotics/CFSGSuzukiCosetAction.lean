import SymmetricSubgroupAsymptotics.CFSGRankOneCosetAction
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality

/-! Doubly transitive action of the pinned original Suzuki matrix model
on its actual Borel cosets, and maximality of that same Borel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiCosetAction
open CFSGSuzukiUnipotent CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow
open CFSGSuzukiOppositeIntersection CFSGSuzukiModelCardinality

abbrev Points (m : ℕ) := ActualGroup m ⧸ modelBorel m

theorem modelBorel_isCoatom (m : ℕ) : IsCoatom (modelBorel m) :=
  CFSGRankOneCosetAction.isCoatom (modelBorel m) (modelUnipotent m) (modelWeyl m)
    (fun _ hx => unipotentSubgroup_le_borelEnvelope m hx)
    (fun hw => weyl_not_mem_borel m hw) (actual_model_two_cells m)

theorem cosetAction_doubly_transitive (m : ℕ) :
    MulAction.IsMultiplyPretransitive (ActualGroup m) (Points m) 2 :=
  CFSGRankOneCosetAction.isMultiplyPretransitive_two
    (modelBorel m) (modelUnipotent m) (modelWeyl m)
    (fun _ hx => unipotentSubgroup_le_borelEnvelope m hx) (actual_model_two_cells m)

theorem cosetAction_primitive (m : ℕ) :
    MulAction.IsPreprimitive (ActualGroup m) (Points m) :=
  CFSGRankOneCosetAction.isPreprimitive
    (modelBorel m) (modelUnipotent m) (modelWeyl m)
    (fun _ hx => unipotentSubgroup_le_borelEnvelope m hx) (actual_model_two_cells m)

theorem base_stabilizer (m : ℕ) :
    MulAction.stabilizer (ActualGroup m) (((1 : ActualGroup m)) : Points m)=modelBorel m :=
  MulAction.stabilizer_quotient (modelBorel m)

end SymmetricSubgroupAsymptotics.CFSGSuzukiCosetAction
