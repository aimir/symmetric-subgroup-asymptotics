import SymmetricSubgroupAsymptotics.FusionPhysicalUnion

/-! Physical relabelling commutes with every invariant predicate on the
complete original subgroup. This retains noncritical filters and earlier
owner exclusions without asking that one local chart be globally fixed.
No eligible-orbit coverage or counting estimate is asserted. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {X Y Ω Z : Type*}

theorem fusionLabelledFamily_relabel
    (P : Subgroup (Equiv.Perm X) → Prop) (e : Equiv.Perm X)
    {H : Subgroup (Equiv.Perm X)} (hH : H ∈ FusionLabelledFamily P) :
    relabelSubgroup e H ∈ FusionLabelledFamily P := by
  obtain ⟨⟨f,K⟩,rfl⟩ := hH
  exact ⟨⟨f.trans e,K⟩,by rw [relabelSubgroup_trans]⟩

/-- A family closed under all physical relabellings is itself invariant,
even if its defining local model is not. -/
theorem fusionLabelledFamily_relabel_iff
    (P : Subgroup (Equiv.Perm X) → Prop) (e : Equiv.Perm X)
    (H : Subgroup (Equiv.Perm X)) :
    relabelSubgroup e H ∈ FusionLabelledFamily P ↔ H ∈ FusionLabelledFamily P := by
  constructor
  · intro hH
    simpa only [relabelSubgroup_symm] using fusionLabelledFamily_relabel P e.symm hH
  · exact fusionLabelledFamily_relabel P e

theorem fusionLabelledFamily_filter
    (P R : Subgroup (Equiv.Perm X) → Prop)
    (hR : ∀ (e : Equiv.Perm X) K, R (relabelSubgroup e K) ↔ R K) :
    FusionLabelledFamily (fun K => P K ∧ R K) =
      {H | H ∈ FusionLabelledFamily P ∧ R H} := by
  ext H
  constructor
  · rintro ⟨⟨e,⟨K,hP,hRK⟩⟩,rfl⟩
    exact ⟨⟨⟨e,⟨K,hP⟩⟩,rfl⟩,(hR e K).mpr hRK⟩
  · rintro ⟨⟨⟨e,⟨K,hP⟩⟩,rfl⟩,hRH⟩
    exact ⟨⟨e,⟨K,hP,(hR e K).mp hRH⟩⟩,rfl⟩

/-- A fixed change of the entire physical point set also preserves the
literal filter. No invariance hypothesis is needed for this one map. -/
theorem fusionRelabelledFamily_filter (e : X ≃ Y)
    (F : Set (Subgroup (Equiv.Perm X))) (R : Subgroup (Equiv.Perm Y) → Prop) :
    FusionRelabelledFamily e {K | K ∈ F ∧ R (relabelSubgroup e K)} =
      {H | H ∈ FusionRelabelledFamily e F ∧ R H} := by
  ext H
  constructor
  · rintro ⟨⟨K,hK,hR⟩,rfl⟩
    exact ⟨⟨⟨K,hK⟩,rfl⟩,hR⟩
  · rintro ⟨⟨⟨K,hK⟩,rfl⟩,hR⟩
    exact ⟨⟨K,hK,hR⟩,rfl⟩

/-- A whole-subgroup physical filter commutes with the complete labelled
orbit family. The full original local subgroup is retained by the map. -/
theorem fusionOrbitFamily_physical_filter
    (U : Subgroup (Equiv.Perm Ω)) (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (R : Subgroup (Equiv.Perm (Ω ⊕ Z)) → Prop)
    (hR : ∀ (e : Equiv.Perm (Ω ⊕ Z)) K, R (relabelSubgroup e K) ↔ R K) :
    FusionOrbitFamily U (fun H => P H ∧ R (H.map (fusionOrbitAction U))) =
      {H | H ∈ FusionOrbitFamily U P ∧ R H} := by
  have hmodel : FusionOrbitModel U
      (fun H => P H ∧ R (H.map (fusionOrbitAction U))) =
      (fun K => FusionOrbitModel U P K ∧ R K) := by
    ext K
    constructor
    · rintro ⟨⟨H,hP,hRH⟩,rfl⟩
      exact ⟨⟨⟨H,hP⟩,rfl⟩,hRH⟩
    · rintro ⟨⟨⟨H,hP⟩,rfl⟩,hRH⟩
      exact ⟨⟨H,hP,hRH⟩,rfl⟩
  unfold FusionOrbitFamily
  rw [hmodel]
  exact fusionLabelledFamily_filter _ R hR

/-- The same identity on any fixed physical labels, keeping the entire
original orbit and complete complement. This supplies the filter comparison
needed before an actual orbit-coverage statement can be used for ownership. -/
theorem fusionPhysicalFamily_filter
    (U : Subgroup (Equiv.Perm Ω)) (e : Ω ⊕ Z ≃ X)
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (R : Subgroup (Equiv.Perm X) → Prop)
    (hR : ∀ (s : Equiv.Perm X) K, R (relabelSubgroup s K) ↔ R K) :
    FusionRelabelledFamily e (FusionOrbitFamily U
      (fun H => P H ∧ R (relabelSubgroup e (H.map (fusionOrbitAction U))))) =
      {H | H ∈ FusionRelabelledFamily e (FusionOrbitFamily U P) ∧ R H} := by
  have hlocal : ∀ (s : Equiv.Perm (Ω ⊕ Z)) K,
      R (relabelSubgroup e (relabelSubgroup s K)) ↔ R (relabelSubgroup e K) := by
    intro s K
    let t : Equiv.Perm X := e.symm.trans (s.trans e)
    have he : e.trans t = s.trans e := by
      ext x
      simp only [t,Equiv.trans_apply,Equiv.symm_apply_apply]
    simpa only [relabelSubgroup_trans,he] using hR t (relabelSubgroup e K)
  rw [fusionOrbitFamily_physical_filter U P
    (fun K => R (relabelSubgroup e K)) hlocal]
  exact fusionRelabelledFamily_filter e _ R

end SymmetricSubgroupAsymptotics
