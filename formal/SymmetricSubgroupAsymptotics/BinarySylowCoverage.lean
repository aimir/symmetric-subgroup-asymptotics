import SymmetricSubgroupAsymptotics.BinaryCoverage

/-!
# Global action coverage from literal local conjugacy edges

A registry is checked only at its supplied representatives. Local index-prime
edges and one actual Sylow root then cover every admissible p-subgroup of the
original ambient group. The conjugating element acts on the original points;
an abstract group isomorphism never substitutes for permutation conjugacy.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Every actual p-subgroup has an ambient conjugate in a chosen Sylow root. -/
theorem pGroup_conjugate_le_chosen_sylow (P : Sylow p G)
    (H : Subgroup G) (hH : IsPGroup p H) :
    ∃ g : G, MulAut.conj g • H ≤ (P : Subgroup G) := by
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff
    (a := MulAut.conj g)).mpr hHQ
  simpa only [← Sylow.coe_subgroup_smul, hg] using h

/-- Membership up to literal ambient conjugation, retaining the supplied
action representative rather than just its abstract isomorphism type. -/
def ActionRegistryCovered {I : Type*} (actions : I → Subgroup G)
    (H : Subgroup G) : Prop :=
  ∃ i : I, ∃ g : G, MulAut.conj g • H = actions i

omit [Finite G] [Fact p.Prime] in
theorem actionRegistryCovered_of_conjugate {I : Type*}
    (actions : I → Subgroup G) (g : G) (H : Subgroup G)
    (h : ActionRegistryCovered actions (MulAut.conj g • H)) :
    ActionRegistryCovered actions H := by
  obtain ⟨i, k, hk⟩ := h
  exact ⟨i, k*g, by simpa only [map_mul, mul_smul] using hk⟩

/-- A locally checked representative registry covers every admissible
p-subgroup. No global coverage assertion is a premise. -/
theorem pGroup_action_registry_complete {I : Type*}
    (actions : I → Subgroup G) (P : Sylow p G)
    (root : I) (hroot : actions root = (P : Subgroup G))
    (A : Subgroup G → Prop)
    (hup : ∀ H K, H ≤ K → A H → A K)
    (hconj : ∀ (g : G) (H : Subgroup G), A H → A (MulAut.conj g • H))
    (hchildren : ∀ i, ∀ K : Subgroup G,
      K < actions i → K.relIndex (actions i) = p → A K →
        ActionRegistryCovered actions K)
    (H : Subgroup G) (hH : IsPGroup p H) (hAH : A H) :
    ActionRegistryCovered actions H := by
  let registry : Set (Subgroup G) := {K | ActionRegistryCovered actions K}
  have hr : (P : Subgroup G) ∈ registry :=
    ⟨root, 1, by simpa using hroot.symm⟩
  have hc : ∀ V ∈ registry, V ≤ (P : Subgroup G) → ∀ K : Subgroup G,
      K < V → K.relIndex V = p → A K → K ∈ registry := by
    intro V hV _ K hKV hidx hAK
    obtain ⟨i, g, hg⟩ := hV
    have hlt : MulAut.conj g • K < actions i := by
      rw [← hg]
      apply lt_iff_le_not_ge.mpr
      exact ⟨Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKV.le,
        fun h => hKV.not_ge (Subgroup.pointwise_smul_le_pointwise_smul_iff.mp h)⟩
    have hi : (MulAut.conj g • K).relIndex (actions i) = p := by
      rw [← hg, Subgroup.relIndex_pointwise_smul, hidx]
    exact actionRegistryCovered_of_conjugate actions g K
      (hchildren i _ hlt hi (hconj g K hAK))
  obtain ⟨g, hg⟩ := pGroup_conjugate_le_chosen_sylow P H hH
  exact actionRegistryCovered_of_conjugate actions g H
    (pGroup_subgroup_registry_complete (P : Subgroup G) P.isPGroup' registry hr
      A hup hc _ hg (hconj g H hAH))

/-- Transitivity on the actual original point set, without changing the
subgroup or choosing a new permutation representation. -/
def PermutationSubgroupTransitive {Ω : Type*} (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ g : Equiv.Perm Ω, g ∈ H ∧ g x = y

theorem permutationSubgroupTransitive_mono {Ω : Type*}
    (H K : Subgroup (Equiv.Perm Ω)) (hHK : H ≤ K)
    (hH : PermutationSubgroupTransitive H) : PermutationSubgroupTransitive K := by
  intro x y
  obtain ⟨g, hg, hxy⟩ := hH x y
  exact ⟨g, hHK hg, hxy⟩

theorem permutationSubgroupTransitive_conjugate {Ω : Type*}
    (g : Equiv.Perm Ω) (H : Subgroup (Equiv.Perm Ω))
    (hH : PermutationSubgroupTransitive H) :
    PermutationSubgroupTransitive (MulAut.conj g • H) := by
  intro x y
  obtain ⟨h, hh, hxy⟩ := hH (g⁻¹ x) (g⁻¹ y)
  refine ⟨MulAut.conj g h, Subgroup.smul_mem_pointwise_smul h (MulAut.conj g) H hh, ?_⟩
  change g (h (g⁻¹ x)) = y
  rw [hxy]
  exact g.apply_symm_apply y

/-- Checking only transitive index-p children of each literal representative
is sufficient for all transitive permutation p-groups of this degree. -/
theorem permutation_pGroup_action_registry_complete {Ω I : Type*} [Finite Ω]
    (actions : I → Subgroup (Equiv.Perm Ω)) (P : Sylow p (Equiv.Perm Ω))
    (root : I) (hroot : actions root = (P : Subgroup (Equiv.Perm Ω)))
    (hchildren : ∀ i, ∀ K : Subgroup (Equiv.Perm Ω),
      K < actions i → K.relIndex (actions i) = p →
      PermutationSubgroupTransitive K → ActionRegistryCovered actions K)
    (H : Subgroup (Equiv.Perm Ω)) (hH : IsPGroup p H)
    (htrans : PermutationSubgroupTransitive H) : ActionRegistryCovered actions H :=
  pGroup_action_registry_complete actions P root hroot PermutationSubgroupTransitive
    permutationSubgroupTransitive_mono permutationSubgroupTransitive_conjugate
    hchildren H hH htrans

end SymmetricSubgroupAsymptotics
