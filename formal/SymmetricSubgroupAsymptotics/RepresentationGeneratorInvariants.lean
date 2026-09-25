import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Fixedness under the original generators determines all invariants.
This algebraic helper is independent of asymptotic counting and capacity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G ι V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixedness is checked on the retained original generators only. -/
theorem binaryPair_invariants_iff_generators
    (ρ : Representation (ZMod 2) G V) (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators)=⊤) (v : V) :
    v∈ρ.invariants ↔ ∀ j, ρ (generators j) v=v := by
  constructor
  · intro h j
    exact h (generators j)
  · intro h
    let S : Subgroup G := {
      carrier := {g | ρ g v=v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ρ (a*b) v=v
        rw [map_mul]
        change ρ a (ρ b v)=v
        rw [hb,ha]
      inv_mem' := by
        intro a ha
        change ρ a⁻¹ v=v
        have he : ρ a⁻¹ (ρ a v)=v := by
          change (ρ a⁻¹*ρ a) v=v
          rw [← map_mul,inv_mul_cancel,map_one]
          rfl
        rwa [ha] at he }
    have ht : S=⊤ := by
      apply top_unique
      rw [← hgen]
      apply (Subgroup.closure_le S).mpr
      rintro _ ⟨j,rfl⟩
      exact h j
    intro g
    exact (show g∈S by rw [ht]; trivial)

end SymmetricSubgroupAsymptotics
