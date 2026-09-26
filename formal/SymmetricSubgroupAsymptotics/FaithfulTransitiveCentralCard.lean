import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.SetTheory.Cardinal.Finite

/-! Central subgroups of a faithful transitive action act freely. If a
central subgroup has as many elements as the original point set, the entire
group acts regularly. These statements use the given original action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G A X : Type*} [Group G] [Group A] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]

/-- An injective central homomorphism is determined by its action at any
one point of a faithful transitive original action. -/
theorem central_evaluation_injective (f : A →* G)
    (hf : Function.Injective f) (hc : ∀ a, f a ∈ Subgroup.center G) (x : X) :
    Function.Injective (fun a : A => f a • x) := by
  intro a b hab
  apply hf
  apply eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  calc
    f a • (g • x) = g • (f a • x) := by
      rw [← mul_smul, ← Subgroup.mem_center_iff.mp (hc a) g, mul_smul]
    _ = g • (f b • x) := congrArg (fun z : X => g • z) hab
    _ = f b • (g • x) := by
      rw [← mul_smul, Subgroup.mem_center_iff.mp (hc b) g, mul_smul]

theorem central_card_le_points [Finite X] (f : A →* G)
    (hf : Function.Injective f) (hc : ∀ a, f a ∈ Subgroup.center G) (x : X) :
    Nat.card A ≤ Nat.card X :=
  Nat.card_le_card_of_injective _ (central_evaluation_injective f hf hc x)

/-- A central subgroup large enough to cover all original points forces
the entire original group to have exactly the point-set cardinality. -/
theorem card_group_eq_points_of_central_card_ge [Finite X] (f : A →* G)
    (hf : Function.Injective f) (hc : ∀ a, f a ∈ Subgroup.center G) (x : X)
    (hcard : Nat.card X ≤ Nat.card A) : Nat.card G = Nat.card X := by
  have hsame : Nat.card A = Nat.card X :=
    (central_card_le_points f hf hc x).antisymm hcard
  have hsurj : Function.Surjective (fun a : A => f a • x) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨central_evaluation_injective f hf hc x, hsame⟩).2
  have hinj : Function.Injective (fun g : G => g • x) := by
    intro g h he
    apply eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨a, rfl⟩ := hsurj y
    calc
      g • (f a • x) = f a • (g • x) := by
        rw [← mul_smul, Subgroup.mem_center_iff.mp (hc a) g, mul_smul]
      _ = f a • (h • x) := congrArg (fun z : X => f a • z) he
      _ = h • (f a • x) := by
        rw [← mul_smul, ← Subgroup.mem_center_iff.mp (hc a) h, mul_smul]
  exact Nat.card_congr (Equiv.ofBijective (fun g : G => g • x)
    ⟨hinj, fun y => MulAction.exists_smul_eq G x y⟩)

/-- A nonregular faithful transitive action has strictly fewer central
elements than original points. The formulation avoids any classification. -/
theorem central_card_lt_points_of_points_lt_group [Finite X] (f : A →* G)
    (hf : Function.Injective f) (hc : ∀ a, f a ∈ Subgroup.center G) (x : X)
    (hlarge : Nat.card X < Nat.card G) : Nat.card A < Nat.card X := by
  by_contra h
  have he := card_group_eq_points_of_central_card_ge f hf hc x (le_of_not_gt h)
  exact (ne_of_lt hlarge) he.symm

end SymmetricSubgroupAsymptotics

end
