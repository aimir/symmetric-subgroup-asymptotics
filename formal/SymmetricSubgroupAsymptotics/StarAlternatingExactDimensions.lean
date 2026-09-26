import SymmetricSubgroupAsymptotics.StarAlternatingParameterCapacity

/-! Exact dimensions for a complete star family under genuine parameter
and vector-space equivalences. A nonzero joint annihilator forces the
original subspace horizontal. A nonzero parameter subspace has an exact
common-radical dimension budget. No independent-pair hypothesis is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k U L V : Type*} [Field k]
    [AddCommGroup U] [Module k U]
    [AddCommGroup L] [Module k L]
    [AddCommGroup V] [Module k V]

variable (F : L →ₗ[k] (V →ₗ[k] V →ₗ[k] k))
    (eL : L ≃ₗ[k] Module.Dual k U) (eV : V ≃ₗ[k] U × k)
    (hF : ∀ l x y, F l x y = starAlternatingFamily (eL l) (eV x) (eV y))

include eL eV hF in
theorem linearJointAnnihilator_horizontal_of_star
    (W : Submodule k V) (hJ : linearJointAnnihilator F W ≠ ⊥) :
    ∀ w ∈ W, (eV w).2 = 0 := by
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hlstar : eL l ∈ linearJointAnnihilator
      (starAlternatingFamily (k := k) (U := U)) (W.map eV.toLinearMap) := by
    rw [linearJointAnnihilator_eq_comap_star F eL eV hF W] at hl
    exact hl
  intro w hw
  by_contra ht
  have hz := starAlternatingFamily_joint_eq_bot_of_last_ne_zero
    (W.map eV.toLinearMap) (eV w) ⟨w, hw, rfl⟩ ht
  rw [hz] at hlstar
  apply hl0
  apply eL.injective
  exact (show eL l = 0 from hlstar).trans (map_zero eL).symm

include eL eV hF in
/-- Whenever the complete actual joint annihilator is nonzero, its
dimension and the actual original subspace dimension sum to dim U. -/
theorem linearJointAnnihilator_finrank_add_eq_of_star [FiniteDimensional k U]
    (W : Submodule k V) (hJ : linearJointAnnihilator F W ≠ ⊥) :
    Module.finrank k W + Module.finrank k (linearJointAnnihilator F W) =
      Module.finrank k U := by
  let W' := W.map eV.toLinearMap
  let J' := linearJointAnnihilator (starAlternatingFamily (k := k) (U := U)) W'
  have hW' : ∀ w ∈ W', w.2 = 0 := by
    rintro w ⟨v, hv, rfl⟩
    exact linearJointAnnihilator_horizontal_of_star F eL eV hF W hJ v hv
  have hdimJ : Module.finrank k (linearJointAnnihilator F W) = Module.finrank k J' := by
    rw [linearJointAnnihilator_eq_comap_star F eL eV hF W]
    exact (eL.ofSubmodule' J').finrank_eq
  rw [hdimJ, ← eV.finrank_map_eq W]
  change Module.finrank k W' + Module.finrank k J' = _
  change Module.finrank k W' + Module.finrank k
    (linearJointAnnihilator (starAlternatingFamily (k := k) (U := U)) W') = _
  rw [starAlternatingFamily_joint_eq_dualAnnihilator W' hW',
    (starHorizontalEquiv W' hW').finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq]

/-- The full common radical of a specified actual parameter subspace. -/
def linearFamilyCommonRadical (P : Submodule k L) : Submodule k V :=
  ⨅ l : P, (F (l : L)).ker

@[simp] theorem mem_linearFamilyCommonRadical_iff (P : Submodule k L) (v : V) :
    v ∈ linearFamilyCommonRadical F P ↔ ∀ l ∈ P, F l v = 0 := by
  simp only [linearFamilyCommonRadical, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]

include eL eV hF in
/-- Both coordinate maps preserve the entire actual parameter subspace
and common radical, rather than a selected list of forms. -/
theorem linearFamilyCommonRadical_map_eq_star (P : Submodule k L) :
    (linearFamilyCommonRadical F P).map eV.toLinearMap =
      starCommonRadical (P.map eL.toLinearMap) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (mem_starCommonRadical_iff _ _).mpr
    rintro l ⟨a, ha, rfl⟩
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := eV.surjective y
    exact (hF a v z).symm.trans
      (LinearMap.congr_fun ((mem_linearFamilyCommonRadical_iff F P v).mp hv a ha) z)
  · intro hx
    refine ⟨eV.symm x, ?_, eV.apply_symm_apply x⟩
    apply (mem_linearFamilyCommonRadical_iff F P _).mpr
    intro a ha
    apply LinearMap.ext
    intro y
    have h := (mem_starCommonRadical_iff _ _).mp hx (eL a) ⟨a, ha, rfl⟩
    have hz : starAlternatingFamily (eL a) (eV (eV.symm x)) (eV y) = 0 := by
      rw [eV.apply_symm_apply]
      exact LinearMap.congr_fun h (eV y)
    exact (hF a (eV.symm x) y).trans hz

include eL eV hF in
theorem linearFamilyCommonRadical_finrank_add_parameter_eq_of_star
    [FiniteDimensional k U] (P : Submodule k L) (hP : P ≠ ⊥) :
    Module.finrank k P + Module.finrank k (linearFamilyCommonRadical F P) =
      Module.finrank k U := by
  have hP' : P.map eL.toLinearMap ≠ ⊥ := by
    intro hz
    apply hP
    apply le_antisymm _ bot_le
    intro a ha
    have hm : eL a ∈ P.map eL.toLinearMap := ⟨a, ha, rfl⟩
    rw [hz] at hm
    change a = 0
    apply eL.injective
    exact (show eL a = 0 from hm).trans (map_zero eL).symm
  have h := starCommonRadical_finrank_add (P.map eL.toLinearMap) hP'
  rw [eL.finrank_map_eq,
    ← linearFamilyCommonRadical_map_eq_star F eL eV hF P, eV.finrank_map_eq] at h
  exact h

end SymmetricSubgroupAsymptotics
