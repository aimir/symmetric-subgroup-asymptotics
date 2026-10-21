import SymmetricSubgroupAsymptotics.CFSGRankOneRootOrbit
import SymmetricSubgroupAsymptotics.CFSGSuzukiCosetAction

/-! Regularity of the actual Suzuki U on all original non-base Borel
cosets. No action identification or abstract Suzuki recognition enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiRootOrbit
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow CFSGSuzukiModelCardinality
open CFSGSuzukiCosetAction

theorem modelWeyl_inv (m : ℕ) : (modelWeyl m)⁻¹=modelWeyl m :=
  Subtype.ext (CFSGSuzukiTorus.weylElement_inv m)

theorem exists_unipotent_transport (m : ℕ) {x : Points m}
    (hx : x≠((1 : ActualGroup m) : Points m)) :
    ∃ u : modelUnipotent m, (u : ActualGroup m) • (modelWeyl m : Points m)=x := by
  simpa only [modelWeyl_inv] using CFSGRankOneRootOrbit.exists_root_transport
    (modelBorel m) (modelUnipotent m) (modelWeyl m) (actual_model_two_cells m) hx

theorem unipotent_transport_injective (m : ℕ) :
    Function.Injective (fun u : modelUnipotent m =>
      (u : ActualGroup m) • (modelWeyl m : Points m)) := by
  simpa only [modelWeyl_inv] using CFSGRankOneRootOrbit.root_transport_injective
    (modelBorel m) (modelUnipotent m) (modelWeyl m) (modelBorel_inf_opposite m)

end SymmetricSubgroupAsymptotics.CFSGSuzukiRootOrbit
