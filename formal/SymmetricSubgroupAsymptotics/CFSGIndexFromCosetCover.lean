import Mathlib.GroupTheory.Index

/-! An actual one-sided coset cover by a homomorphism computes the
subgroup index through its literal comap. No normality is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIndexFromCosetCover
variable {A G : Type*} [Group A] [Group G]

theorem index_comap_eq_of_coset_cover (H : Subgroup G) (f : A →* G)
    (hcover : ∀ g : G, ∃ a : A, (f a)⁻¹ * g ∈ H) : (H.comap f).index = H.index := by
  have key : ∀ x y : A, QuotientGroup.leftRel (H.comap f) x y ↔
      QuotientGroup.leftRel H (f x) (f y) := by
    intro x y
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, map_mul, map_inv]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' f (fun x y => (key x y).mp)) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' (fun x => ?_)
    refine Quotient.ind' (fun y => ?_)
    exact (key x y).mpr
  · refine Quotient.ind' (fun g => ?_)
    obtain ⟨a, ha⟩ := hcover g
    refine ⟨Quotient.mk'' a, ?_⟩
    change (Quotient.mk'' (f a) : G ⧸ H) = Quotient.mk'' g
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr ha

theorem index_le_of_parameter_subgroup [Finite A] (H : Subgroup G) (f : A →* G)
    (N : Subgroup A) (hN : N ≤ H.comap f)
    (hcover : ∀ g : G, ∃ a : A, (f a)⁻¹ * g ∈ H) : H.index ≤ N.index := by
  rw [← index_comap_eq_of_coset_cover H f hcover]
  exact Subgroup.index_antitone hN

end SymmetricSubgroupAsymptotics.CFSGIndexFromCosetCover
