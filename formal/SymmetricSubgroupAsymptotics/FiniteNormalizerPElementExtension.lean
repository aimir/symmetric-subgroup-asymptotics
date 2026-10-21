import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Finite

/-! A selected prime-power-order element in the actual seed normalizer
produces a strictly larger prime-power subgroup. Its actual inclusion is
retained, so an existing action registry can classify the extension without
a second search for point conjugators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension

variable {G : Type*} [Group G] {p : ℕ}

/-- One power equation certifies the entire cyclic subgroup. -/
theorem zpowers_isPGroup (n : G) (k : ℕ) (hn : n ^ (p ^ k) = 1) :
    IsPGroup p (Subgroup.zpowers n) := by
  intro x
  refine ⟨k, Subtype.ext ?_⟩
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp x.property
  change x.val ^ (p ^ k) = 1
  rw [← hz, ← zpow_natCast, ← zpow_mul, mul_comm z ((p ^ k : ℕ) : ℤ), zpow_mul,
    zpow_natCast, hn, one_zpow]

/-- No index or order table is needed: normalizer membership and one power
relation prove that the actual join is a prime-power group. -/
theorem extension_isPGroup (H : Subgroup G) (hH : IsPGroup p H)
    (n : G) (k : ℕ) (hn : n ^ (p ^ k) = 1)
    (hnorm : n ∈ Subgroup.normalizer H) :
    IsPGroup p (H ⊔ Subgroup.zpowers n : Subgroup G) :=
  hH.to_sup_of_normal_left' (zpowers_isPGroup n k hn)
    (Subgroup.zpowers_le.mpr hnorm)

theorem extension_le (H U : Subgroup G) (hHU : H ≤ U)
    (n : G) (hnU : n ∈ U) : H ⊔ Subgroup.zpowers n ≤ U :=
  sup_le hHU (Subgroup.zpowers_le.mpr hnU)

/-- A literal nonmembership witness forces a strictly larger seed. -/
theorem card_lt_extension [Finite G] (H : Subgroup G) (n : G) (hnH : n ∉ H) :
    Nat.card H < Nat.card (H ⊔ Subgroup.zpowers n : Subgroup G) := by
  apply lt_of_not_ge
  intro hcard
  have heq : H = H ⊔ Subgroup.zpowers n :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  apply hnH
  rw [heq]
  exact (show Subgroup.zpowers n ≤ H ⊔ Subgroup.zpowers n from le_sup_right)
    (Subgroup.mem_zpowers n)

end SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension
end
