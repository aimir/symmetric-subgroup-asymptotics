import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-!
# Conjugacy from original generators and exact finite indices

A literal target is contained in the conjugated child once the inverse
conjugates of its original generators belong to that child. The actual
relative index and exact original cardinalities then force equality.
No whole-row correspondence or global registry-coverage premise is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

/-- The actual subgroup cardinality and its relative index recover its
original overgroup cardinality. The formula is valid without assuming the
whole ambient group is finite. -/
theorem subgroup_card_mul_relIndex_of_le {K U : Subgroup G} (hKU : K ≤ U) :
    Nat.card K * K.relIndex U = Nat.card U := by
  simpa only [Subgroup.relIndex_bot_left] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) K U bot_le hKU

/-- One literal inclusion and equal finite cardinality suffice to prove
original ambient conjugacy, rather than an abstract group isomorphism. -/
theorem subgroup_conjugate_eq_of_le_card {K T : Subgroup G} [Finite K]
    (g : G) (hle : T ≤ MulAut.conj g • K) (hcard : Nat.card T = Nat.card K) :
    MulAut.conj g • K = T := by
  let e := (Subgroup.equivSMul (MulAut.conj g) K).toEquiv
  letI : Finite ↥(MulAut.conj g • K) := Finite.of_equiv K e
  apply (Subgroup.eq_of_le_of_card_ge hle _).symm
  rw [← Nat.card_congr e,hcard]

/-- General finite-index compression. All cardinalities belong to the
actual embedded subgroups, and the same original g provides conjugacy. -/
theorem subgroup_conjugate_eq_of_relIndex_card {K U T : Subgroup G} [Finite U]
    (g : G) (hKU : K ≤ U) {r : ℕ} (hr : r ≠ 0)
    (hindex : K.relIndex U = r) (hcard : Nat.card T * r = Nat.card U)
    (hle : T ≤ MulAut.conj g • K) : MulAut.conj g • K = T := by
  letI : Finite K := Finite.of_injective (Subgroup.inclusion hKU)
    (Subgroup.inclusion_injective hKU)
  have hKcard : Nat.card K * r = Nat.card U := by
    rw [← hindex]
    exact subgroup_card_mul_relIndex_of_le hKU
  apply subgroup_conjugate_eq_of_le_card g hle
  exact mul_right_cancel₀ hr (hcard.trans hKcard.symm)

/-- Small inverse-generator witnesses prove the required literal inclusion. -/
theorem generated_target_le_conjugate {ι : Type*} (generators : ι → G)
    (K : Subgroup G) (g : G)
    (hgens : ∀ j, MulAut.conj g⁻¹ (generators j) ∈ K) :
    Subgroup.closure (Set.range generators) ≤ MulAut.conj g • K := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  have h := Subgroup.smul_mem_pointwise_smul
    (MulAut.conj g⁻¹ (generators j)) (MulAut.conj g) K (hgens j)
  change MulAut.conj g (MulAut.conj g⁻¹ (generators j)) ∈ MulAut.conj g • K at h
  simpa [MulAut.conj_apply,mul_assoc] using h

/-- The exporter-facing index-two bridge, for an arbitrary actual finite
source action and a target given by its original generating permutations. -/
theorem binary_generator_conjugacy {ι : Type*} (generators : ι → G)
    {K U : Subgroup G} [Finite U] (g : G) (hKU : K ≤ U)
    (hindex : K.relIndex U = 2)
    (hcard : Nat.card (Subgroup.closure (Set.range generators)) * 2 = Nat.card U)
    (hgens : ∀ j, MulAut.conj g⁻¹ (generators j) ∈ K) :
    MulAut.conj g • K = Subgroup.closure (Set.range generators) :=
  subgroup_conjugate_eq_of_relIndex_card g hKU (by decide) hindex hcard
    (generated_target_le_conjugate generators K g hgens)

/-- Both original actions may be supplied by their original generators.
This is the precise literal child certificate used by finite action menus. -/
theorem binary_generated_source_conjugacy {ι κ : Type*}
    (sourceGenerators : ι → G) (targetGenerators : κ → G)
    [Finite (Subgroup.closure (Set.range sourceGenerators))]
    (K : Subgroup G) (g : G)
    (hKU : K ≤ Subgroup.closure (Set.range sourceGenerators))
    (hindex : K.relIndex (Subgroup.closure (Set.range sourceGenerators)) = 2)
    (hcard : Nat.card (Subgroup.closure (Set.range targetGenerators)) * 2 =
      Nat.card (Subgroup.closure (Set.range sourceGenerators)))
    (hgens : ∀ j, MulAut.conj g⁻¹ (targetGenerators j) ∈ K) :
    MulAut.conj g • K = Subgroup.closure (Set.range targetGenerators) :=
  binary_generator_conjugacy targetGenerators g hKU hindex hcard hgens

end SymmetricSubgroupAsymptotics
