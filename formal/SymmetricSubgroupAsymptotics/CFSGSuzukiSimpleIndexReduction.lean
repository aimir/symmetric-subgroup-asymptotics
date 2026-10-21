import SymmetricSubgroupAsymptotics.CFSGSimpleIndexRemainingModels
import SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound

/-! Exact simple-index dispatch after proving the pinned Suzuki family.
Only that proved family is removed from the existing open callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def RemainingSimpleIndexModelWithoutSuzuki : CFSG.Index→Prop
  | .suzuki _ _ => False
  | i => RemainingSimpleIndexModel i

theorem simpleIndex_model_or_remaining_without_suzuki (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i∨RemainingSimpleIndexModelWithoutSuzuki i := by
  cases i <;> try exact simpleIndex_model_or_remaining _ hn
  case suzuki m hm hsimple =>
    letI : IsSimpleGroup (CFSG.Models.Suzuki m) := hsimple
    exact Or.inl (CFSGSuzukiOuterBound.simpleIndexBounds m hm)

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_suzuki_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingSimpleIndexModelWithoutSuzuki i→ModelSimpleIndexBounds i) :
    PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_models hCFSG
  intro i _ _ hn hi
  cases i <;> try exact remaining _ hn hi
  case suzuki m hm hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.Suzuki m) := hsimple
    exact CFSGSuzukiOuterBound.simpleIndexBounds m hm

end SymmetricSubgroupAsymptotics.CFSGReduction
