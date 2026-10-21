import SymmetricSubgroupAsymptotics.FiniteLeftCosetAdjunctionCoverage
import Mathlib.Logic.Equiv.Fin.Basic

/-! Compose actual left-coset covers through an intermediate subgroup.
Only the intermediate subgroup's generator edges require new finite checks;
a proved larger ambient cover can be reused without a full new action table. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G I : Type*} [Group G]

namespace FiniteLeftCosetCover
variable {generators : I → G} {H : Subgroup G} {q : ℕ}
  (C : FiniteLeftCosetCover generators H q)

/-- A cover certificate applies to the actual generated subgroup even when
its generator family does not generate the entire ambient group. -/
theorem covers_mem (g : G) (hg : g ∈ Subgroup.closure (Set.range generators)) :
    ∃ i : Fin q, g * (C.representatives i)⁻¹ ∈ H := by
  let S : Set G := {x | ∃ i : Fin q, x * (C.representatives i)⁻¹ ∈ H}
  have hOne : (1 : G) ∈ S :=
    ⟨C.identity, by simpa only [one_mul] using H.inv_mem C.identity_mem⟩
  let R : Subgroup G := {
    carrier := {a | (∀ x ∈ S, x * a ∈ S) ∧ (∀ x ∈ S, x * a⁻¹ ∈ S)}
    one_mem' := by constructor <;> intro x hx <;> simpa using hx
    mul_mem' := by
      intro a b ha hb
      constructor
      · intro x hx
        simpa only [mul_assoc] using hb.1 (x * a) (ha.1 x hx)
      · intro x hx
        simpa only [mul_inv_rev, mul_assoc] using ha.2 (x * b⁻¹) (hb.2 x hx)
    inv_mem' := by
      intro a ha
      exact ⟨ha.2, by simpa only [inv_inv] using ha.1⟩ }
  have hle : Subgroup.closure (Set.range generators) ≤ R := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    constructor
    · rintro x ⟨i, hi⟩
      refine ⟨C.next i j, ?_⟩
      have he := H.mul_mem hi (C.step_mem i j)
      convert he using 1; group
    · rintro x ⟨i, hi⟩
      refine ⟨C.prev i j, ?_⟩
      have he := H.mul_mem hi (C.inverse_step_mem i j)
      convert he using 1; group
  have hgR : g ∈ R := hle hg
  simpa only [one_mul] using hgR.1 1 hOne

end FiniteLeftCosetCover

/-- Literal products of representatives cover through the intermediate
subgroup. Normality is not required for either inclusion. -/
theorem leftCoset_covers_compose
    {H P : Subgroup G} {J K : Type*}
    (localRepresentatives : J → G) (ambientRepresentatives : K → G)
    (hlocal : ∀ p ∈ P, ∃ j, p * (localRepresentatives j)⁻¹ ∈ H)
    (hambient : ∀ g : G, ∃ k, g * (ambientRepresentatives k)⁻¹ ∈ P)
    (g : G) :
    ∃ jk : J × K,
      g * (localRepresentatives jk.1 * ambientRepresentatives jk.2)⁻¹ ∈ H := by
  obtain ⟨k, hk⟩ := hambient g
  obtain ⟨j, hj⟩ := hlocal (g * (ambientRepresentatives k)⁻¹) hk
  refine ⟨(j, k), ?_⟩
  simpa only [mul_inv_rev, mul_assoc] using hj

/-- A finite local generator-edge certificate composes with any retained
actual ambient cover. -/
theorem FiniteLeftCosetCover.covers_compose
    {generators : I → G} {H : Subgroup G} {q : ℕ}
    (C : FiniteLeftCosetCover generators H q) {K : Type*}
    (ambientRepresentatives : K → G)
    (hambient : ∀ g : G, ∃ k,
      g * (ambientRepresentatives k)⁻¹ ∈ Subgroup.closure (Set.range generators))
    (g : G) :
    ∃ jk : Fin q × K,
      g * (C.representatives jk.1 * ambientRepresentatives jk.2)⁻¹ ∈ H :=
  leftCoset_covers_compose C.representatives ambientRepresentatives
    (fun p hp => C.covers_mem p hp) hambient g

end SymmetricSubgroupAsymptotics
end
