import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentBorel
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusElements
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-! The exact original Suzuki generator partition into its actual Borel
envelope and the actual displayed Weyl element. No Bruhat identity is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSG.Models.SuzukiConstruction CFSGSuzukiTorus

theorem model_eq_borel_sup_weyl (m : ℕ) :
    subgroup m = borelEnvelope m ⊔ Subgroup.zpowers (weylElement m) := by
  have hBle : borelEnvelope m ≤ borelEnvelope m ⊔ Subgroup.zpowers (weylElement m) := le_sup_left
  have hWle : Subgroup.zpowers (weylElement m) ≤ borelEnvelope m ⊔ Subgroup.zpowers (weylElement m) := le_sup_right
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨a, b, h⟩ | ⟨c, h⟩ | h
    · apply hBle
      apply unipotentSubgroup_le_borelEnvelope m
      exact ⟨a, b, Units.ext h⟩
    · exact hBle (torus_mem_borelEnvelope m g c h)
    · have hg : g = weylElement m := Units.ext h
      rw [hg]
      exact hWle (Subgroup.mem_zpowers _)
  · exact sup_le (borelEnvelope_le_model m)
      (Subgroup.zpowers_le.mpr (weylElement_mem_model m))

theorem closure_borel_weyl (m : ℕ) :
    Subgroup.closure ((borelEnvelope m : Set (Ambient m)) ∪ {weylElement m}) = subgroup m := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure,
    ← model_eq_borel_sup_weyl]

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
