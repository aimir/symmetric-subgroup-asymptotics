import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Moving orbits of a three-group cost at least three original points.
The fixed points and the full moving orbits inject disjointly into the
original action. This gives the sixteen-point bound without a row census. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount

variable (P X : Type) [Group P] [MulAction P X]

abbrev movingOrbits :=
  {q : MulAction.orbitRel.Quotient P X // 1 < Nat.card q.orbit}

abbrev movingPoints := Σ q : movingOrbits P X, q.1.orbit

def movingPoint : movingPoints P X → X := fun z => z.2.1

theorem movingPoint_injective : Function.Injective (movingPoint P X) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have hxy : (x : X) = (y : X) := h
  have hab : a.1 = b.1 :=
    (MulAction.orbitRel.Quotient.mem_orbit.mp x.2).symm.trans
      ((congrArg (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient P X)) hxy).trans
        (MulAction.orbitRel.Quotient.mem_orbit.mp y.2))
  have hab' : a = b := Subtype.ext hab
  subst b
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

theorem movingPoint_not_fixed [Finite X] (z : movingPoints P X) :
    movingPoint P X z ∉ MulAction.fixedPoints P X := by
  intro hfixed
  letI : Fintype (MulAction.orbit P (movingPoint P X z)) := Fintype.ofFinite _
  have hone := MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hfixed
  have horbit : z.1.1.orbit = MulAction.orbit P (movingPoint P X z) := by
    rw [← MulAction.orbitRel.Quotient.mem_orbit.mp z.2.2]
    rfl
  have hgt := z.1.2
  rw [horbit, Nat.card_eq_fintype_card, hone] at hgt
  omega

def fixedAndMoving : MulAction.fixedPoints P X ⊕ movingPoints P X → X :=
  Sum.elim Subtype.val (movingPoint P X)

theorem fixedAndMoving_injective [Finite X] :
    Function.Injective (fixedAndMoving P X) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
          change (a : X) = movingPoint P X b at h
          have hf : movingPoint P X b ∈ MulAction.fixedPoints P X := h ▸ a.2
          exact False.elim (movingPoint_not_fixed P X b hf)
  | inr a =>
      cases b with
      | inl b =>
          change movingPoint P X a = (b : X) at h
          have hf : movingPoint P X a ∈ MulAction.fixedPoints P X := h.symm ▸ b.2
          exact False.elim (movingPoint_not_fixed P X a hf)
      | inr b => exact congrArg Sum.inr (movingPoint_injective P X h)

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem three_le_moving_orbit [Finite X] (hP : IsPGroup 3 P)
    (q : movingOrbits P X) : 3 ≤ Nat.card q.1.orbit := by
  have he := MulAction.orbitRel.Quotient.orbit_eq_orbit_out q.1 Quotient.out_eq'
  obtain ⟨n, hn⟩ := hP.card_orbit q.1.out
  have hcard : Nat.card q.1.orbit = 3 ^ n := by rw [he]; exact hn
  have hnpos : 1 ≤ n := by
    by_contra h
    have hnzero : n = 0 := by omega
    have hgt := q.2
    rw [hcard, hnzero, pow_zero] at hgt
    omega
  rw [hcard]
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hnpos

/-- The weighted orbit inequality keeps the original fixed-point set. -/
theorem fixed_add_three_mul_moving_le [Finite X] (hP : IsPGroup 3 P) :
    Nat.card (MulAction.fixedPoints P X) + 3 * Nat.card (movingOrbits P X) ≤
      Nat.card X := by
  letI : Fintype (movingOrbits P X) := Fintype.ofFinite _
  have hsum : 3 * Nat.card (movingOrbits P X) ≤ Nat.card (movingPoints P X) := by
    rw [Nat.card_sigma]
    calc
      _ = ∑ _q : movingOrbits P X, 3 := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun q _ => three_le_moving_orbit P X hP q)
  have hinj := Nat.card_le_card_of_injective (fixedAndMoving P X)
    (fixedAndMoving_injective P X)
  rw [Nat.card_sum] at hinj
  omega

/-- Four fixed points in a sixteen-point action leave at most four
moving ternary orbits. -/
theorem moving_le_four [Finite X] (hP : IsPGroup 3 P)
    (hX : Nat.card X = 16) (hfixed : 4 ≤ Nat.card (MulAction.fixedPoints P X)) :
    Nat.card (movingOrbits P X) ≤ 4 := by
  have h := fixed_add_three_mul_moving_le P X hP
  omega

end SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount

end
