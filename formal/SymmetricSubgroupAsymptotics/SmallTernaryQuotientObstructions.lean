import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple

/-! Structural obstructions to the local quotients in a binary affine
plane. These use actual homomorphisms, not a list of candidate kernel
orders. They apply to the four excluded primitive eight-point stabilizers.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A homomorphism from a larger finite simple group to a smaller group is
trivial, including when the displayed target is not its actual image. -/
theorem simpleHom_eq_one_of_card_lt
    {G Q : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [Group Q] [Finite Q] (f : G →* Q) (hcard : Nat.card Q < Nat.card G) :
    ∀ g : G, f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with hk | hk
  · have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
    exact False.elim (Nat.not_le_of_gt hcard (Nat.card_le_card_of_injective f hi))
  · intro g
    exact MonoidHom.mem_ker.mp (show g ∈ f.ker by rw [hk]; trivial)

/-- Killing a subgroup of index at most two precludes any onto target of
order three or six. Normality of the displayed subgroup is unnecessary. -/
theorem not_surjective_three_or_six_of_small_index
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (K : Subgroup G) (hindex : K.index ≤ 2) (f : G →* Q)
    (hkill : ∀ k : K, f k = 1)
    (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  intro hf
  have hle : K ≤ f.ker := fun k hk => MonoidHom.mem_ker.mpr (hkill ⟨k, hk⟩)
  have hdiv := Subgroup.index_dvd_of_le hle
  have hcard : f.ker.index = Nat.card Q := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hcard] at hdiv
  have hpos : 0 < K.index := Nat.pos_of_ne_zero K.index_ne_zero_of_finite
  have hbound := Nat.le_of_dvd hpos hdiv
  rcases hQ with hQ | hQ <;> omega

/-- The simple stabilizer cases and the index-two almost-simple case use
the same argument. The index and the actual simple subgroup are retained. -/
theorem not_surjective_three_or_six_of_simple_subgroup
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (K : Subgroup G) [IsSimpleGroup K]
    (hindex : K.index ≤ 2) (hcard : 6 < Nat.card K)
    (f : G →* Q) (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  apply not_surjective_three_or_six_of_small_index K hindex f _ hQ
  exact simpleHom_eq_one_of_card_lt (f.comp K.subtype) (by
    rcases hQ with hQ | hQ <;> omega)

/-- In particular a simple group of order greater than six is ineligible. -/
theorem not_surjective_three_or_six_of_simple
    {G Q : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [Group Q] [Finite Q] (hcard : 6 < Nat.card G)
    (f : G →* Q) (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  apply not_surjective_three_or_six_of_small_index (⊤ : Subgroup G) (by simp) f _ hQ
  intro g
  exact simpleHom_eq_one_of_card_lt f (by
    rcases hQ with hQ | hQ <;> omega) g.1

end SymmetricSubgroupAsymptotics

end
