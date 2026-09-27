import SymmetricSubgroupAsymptotics.CharacterCollisionCount
import SymmetricSubgroupAsymptotics.CharacterIndependentSelections
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fourth moment of original character occurrences

The excess over seven occurrences and the actual unordered duplicate marks
has fourth power bounded by the actual ordered independent four-selections.
Two applications of finite Cauchy--Schwarz give the aggregate inequality.
This keeps the physical incidence bounds as explicit later inputs: it does
not assume that independently chosen coordinates already define a fusion.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.CharacterPairMoment

variable {I V : Type*} [Finite I] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : I → V)

def excess : ℕ := Nat.card I - (7 + Nat.card (CharacterCollisionCount.Collision f))

theorem card_le_seven_add_collisions_add_excess :
    Nat.card I ≤ 7 + Nat.card (CharacterCollisionCount.Collision f) + excess f := by
  unfold excess
  omega

theorem excess_pow_four_le_frames (hzero : ∀ i, f i ≠ 0) :
    excess f ^ 4 ≤ Nat.card (CharacterIndependentSelections.Frame f 4) := by
  have hc := CharacterCollisionCount.card_le_distinct_add_collisions f
  have he : excess f ≤ Nat.card (Set.range f) - 7 := by
    unfold excess
    omega
  exact (Nat.pow_le_pow_left he 4).trans
    (CharacterIndependentSelections.four_frame_card_lower f hzero)

/-- A root-free fourth-moment estimate for a finite family. -/
theorem sum_pow_four_le_card_cube_mul_sum {B : Type*} [Fintype B] (a : B → ℕ) :
    (∑ b, a b) ^ 4 ≤ Fintype.card B ^ 3 * ∑ b, a b ^ 4 := by
  have h₁ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : B => (1 : ℕ)) a
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : B => (1 : ℕ))
    (fun b => a b ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one] at h₁ h₂
  calc
    (∑ b, a b) ^ 4 = ((∑ b, a b) ^ 2) ^ 2 := by ring
    _ ≤ (Fintype.card B * ∑ b, a b ^ 2) ^ 2 := Nat.pow_le_pow_left h₁ 2
    _ = Fintype.card B ^ 2 * (∑ b, a b ^ 2) ^ 2 := by ring
    _ ≤ Fintype.card B ^ 2 * (Fintype.card B * ∑ b, (a b ^ 2) ^ 2) :=
      Nat.mul_le_mul_left _ h₂
    _ = Fintype.card B ^ 3 * ∑ b, a b ^ 4 := by
      simp only [← pow_mul]
      ring

section Family

variable {B : Type*} [Fintype B] {I V : B → Type*}
    [∀ b, Finite (I b)] [∀ b, AddCommGroup (V b)]
    [∀ b, Module (ZMod 2) (V b)] [∀ b, Finite (V b)]
    (f : ∀ b, I b → V b)

/-- Different original groups may have different character spaces. Every
collision and independent selection still belongs to its original group. -/
theorem aggregate_excess_pow_four_le (hzero : ∀ b i, f b i ≠ 0) :
    (∑ b, excess (f b)) ^ 4 ≤ Fintype.card B ^ 3 *
      ∑ b, Nat.card (CharacterIndependentSelections.Frame (f b) 4) := by
  exact (sum_pow_four_le_card_cube_mul_sum (fun b => excess (f b))).trans
    (Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun b _ =>
      excess_pow_four_le_frames (f b) (hzero b))))

theorem aggregate_card_le :
    (∑ b, Nat.card (I b)) ≤ 7 * Fintype.card B +
      (∑ b, Nat.card (CharacterCollisionCount.Collision (f b))) + ∑ b, excess (f b) := by
  have h := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset B)) =>
    card_le_seven_add_collisions_add_excess (f b))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm] using h

end Family

end SymmetricSubgroupAsymptotics.CharacterPairMoment
