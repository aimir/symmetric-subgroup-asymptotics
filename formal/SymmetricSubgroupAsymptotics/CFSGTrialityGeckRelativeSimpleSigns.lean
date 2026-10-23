import SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage

/-! The three outer simple images of an actual relative Weyl word have
one sign, by literal triality covariance. This is integral root-lattice
data and makes no field-size or group recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeSimpleSigns
open CFSGTrialityD4NormTwo CFSGTrialityD4WordDiscriminant
open CFSGTrialityRelativeWordLanguage CFSGTrialityD4InvariantRoots
open CFSGNormTwoRootPairing
local notation "A" => CartanMatrix.D 4

theorem diagramRoot_nonnegative (k : Roots A) (hk : ∀i,0≤k.val i) :
    ∀i,0≤(diagramRoot k).val i := by
  intro i
  exact hk _

theorem diagramRoot_nonpositive (k : Roots A) (hk : ∀i,k.val i≤0) :
    ∀i,(diagramRoot k).val i≤0 := by
  intro i
  exact hk _

theorem relative_outer_images_nonnegative (r : List Bool)
    (h0 : ∀i,0≤(rootAction (expandRelative r) (Index 0)).val i)
    (j : Fin 4) (hj : j≠1) : ∀i,0≤(rootAction (expandRelative r) (Index j)).val i := by
  have h02 := relative_root_action_commutes r (Index 0)
  rw [diagramRoot_index] at h02
  change diagramRoot (rootAction (expandRelative r) (Index 0))=
    rootAction (expandRelative r) (Index 2) at h02
  have h2 : ∀i,0≤(rootAction (expandRelative r) (Index 2)).val i := by
    rw [←h02]
    exact diagramRoot_nonnegative _ h0
  have h23 := relative_root_action_commutes r (Index 2)
  rw [diagramRoot_index] at h23
  change diagramRoot (rootAction (expandRelative r) (Index 2))=
    rootAction (expandRelative r) (Index 3) at h23
  have h3 : ∀i,0≤(rootAction (expandRelative r) (Index 3)).val i := by
    rw [←h23]
    exact diagramRoot_nonnegative _ h2
  fin_cases j
  · exact h0
  · exact False.elim (hj rfl)
  · exact h2
  · exact h3

theorem relative_simple_images_nonpositive (r : List Bool)
    (h0 : ∀i,(rootAction (expandRelative r) (Index 0)).val i≤0)
    (h1 : ∀i,(rootAction (expandRelative r) (Index 1)).val i≤0)
    (j : Fin 4) : ∀i,(rootAction (expandRelative r) (Index j)).val i≤0 := by
  have h02 := relative_root_action_commutes r (Index 0)
  rw [diagramRoot_index] at h02
  change diagramRoot (rootAction (expandRelative r) (Index 0))=
    rootAction (expandRelative r) (Index 2) at h02
  have h2 : ∀i,(rootAction (expandRelative r) (Index 2)).val i≤0 := by
    rw [←h02]
    exact diagramRoot_nonpositive _ h0
  have h23 := relative_root_action_commutes r (Index 2)
  rw [diagramRoot_index] at h23
  change diagramRoot (rootAction (expandRelative r) (Index 2))=
    rootAction (expandRelative r) (Index 3) at h23
  have h3 : ∀i,(rootAction (expandRelative r) (Index 3)).val i≤0 := by
    rw [←h23]
    exact diagramRoot_nonpositive _ h2
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeSimpleSigns
