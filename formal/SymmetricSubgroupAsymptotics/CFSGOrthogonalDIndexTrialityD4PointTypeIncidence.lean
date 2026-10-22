import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeAction

/-! The constructed actual point action preserves the actual
point/plane incidence in both directions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem pointTypeAction_incidence_forward (f : naturalPointTypeStabilizer K p)
    (U : OriginalPoints K) (P : SingularPlanes K 0) (hUP : U.val ≤ P.val) :
    (pointTypeAction K p f U).val ≤ (singularActionHom K p 0 f.val P).val := by
  obtain ⟨S, hS, hP⟩ := incident_pair_in_star K U P hUP
  have hi : singularActionHom K p 0 f.val P ∈ pointStarPlanes K (starLabelAction K p f S) := by
    rw [starLabelAction_sets]
    exact ⟨P, hP, rfl⟩
  have he : pointTypeAction K p f U = pointOfStar K (starLabelAction K p f S) := by
    rw [← hS]
    exact pointTypeAction_of_star K p f S
  rw [he]
  exact hi.1

theorem pointTypeAction_incidence (f : naturalPointTypeStabilizer K p)
    (U : OriginalPoints K) (P : SingularPlanes K 0) :
    (pointTypeAction K p f U).val ≤ (singularActionHom K p 0 f.val P).val ↔ U.val ≤ P.val := by
  constructor
  · intro h
    have hh := pointTypeAction_incidence_forward K p f⁻¹ (pointTypeAction K p f U)
      (singularActionHom K p 0 f.val P) h
    simpa only [map_inv, Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hh
  · exact pointTypeAction_incidence_forward K p f U P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
