import SymmetricSubgroupAsymptotics.BinaryCarrierMixtureCompletion

/-! Relabelling closure of literal profile unions and of the complete
finite-alphabet mixture. Relabelling changes the existential chart, leaving
the original model subgroup and its predicate unchanged. Thus no invariance
assumption on that model predicate is needed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- An arbitrary union of original model profiles is natural in the final
labelled point set, even if the model predicates themselves are arbitrary. -/
def assembledOrbitProfilesRelabelEquiv {τ ι X Y : Type*} {Ω : ι → Type*}
    (m : τ → ι → ℕ)
    (P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop)
    (e : X ≃ Y) :
    AssembledOrbitProfilesOn m P X ≃ AssembledOrbitProfilesOn m P Y where
  toFun H := ⟨relabelSubgroup e H.1, by
    obtain ⟨t, f, K, hK, hH⟩ := H.2
    refine ⟨t, f.trans e, K, hK, ?_⟩
    rw [← relabelSubgroup_trans, hH]⟩
  invFun H := ⟨relabelSubgroup e.symm H.1, by
    obtain ⟨t, f, K, hK, hH⟩ := H.2
    refine ⟨t, f.trans e.symm, K, hK, ?_⟩
    rw [← relabelSubgroup_trans, hH]⟩
  left_inv H := Subtype.ext (relabelSubgroup_symm e H.1)
  right_inv H := Subtype.ext (by simpa using relabelSubgroup_symm e.symm H.1)

@[simp] theorem assembledOrbitProfilesRelabelEquiv_val {τ ι X Y : Type*} {Ω : ι → Type*}
    (m : τ → ι → ℕ)
    (P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop)
    (e : X ≃ Y) (H : AssembledOrbitProfilesOn m P X) :
    (assembledOrbitProfilesRelabelEquiv m P e H).1 = relabelSubgroup e H.1 := rfl

namespace BinaryCarrierMixtureCompletion

/-- Every original parameter witness remains valid after ambient relabelling. -/
def relabelFamily (n : ℕ) (e : Equiv.Perm (Fin (2*n))) (H : Family n) : Family n :=
  ⟨relabelSubgroup e H.1, by
    obtain ⟨b, K, hK⟩ := H.2
    let K' := assembledOrbitProfilesRelabelEquiv
      (BinaryCarrierParameterProfiles.profileMultiplicity
        (n-(2*b.1.1+4*b.1.2)) b.1.1 b.1.2)
      (BinaryCarrierParameterProfiles.profilePredicate
        (n-(2*b.1.1+4*b.1.2)) b.1.1 b.1.2) e K
    refine ⟨b, K', ?_⟩
    exact congrArg (relabelSubgroup e) hK⟩

@[simp] theorem relabelFamily_val (n : ℕ) (e : Equiv.Perm (Fin (2*n)))
    (H : Family n) : (relabelFamily n e H).1 = relabelSubgroup e H.1 := rfl

/-- Actual conjugacy closure, suitable for changing a singleton complement
chart without introducing an extra labelling factorial. -/
def relabelFamilyEquiv (n : ℕ) (e : Equiv.Perm (Fin (2*n))) : Family n ≃ Family n where
  toFun := relabelFamily n e
  invFun := relabelFamily n e.symm
  left_inv H := Subtype.ext (relabelSubgroup_symm e H.1)
  right_inv H := Subtype.ext (by simpa using relabelSubgroup_symm e.symm H.1)

@[simp] theorem relabelFamilyEquiv_val (n : ℕ) (e : Equiv.Perm (Fin (2*n)))
    (H : Family n) : (relabelFamilyEquiv n e H).1 = relabelSubgroup e H.1 := rfl

end BinaryCarrierMixtureCompletion
end SymmetricSubgroupAsymptotics
