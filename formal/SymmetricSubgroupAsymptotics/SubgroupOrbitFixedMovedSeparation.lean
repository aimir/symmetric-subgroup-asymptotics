import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Card

/-! Two genuine subgroup orbits are disjoint when one fixes an element
pointwise and the other consists of points moved by it. This couples
local actions inside one original global action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SubgroupOrbitFixedMovedSeparation
variable {G X : Type*} [Group G] [MulAction G X] [Finite X]

theorem orbit_card_add_le (P Q : Subgroup G) (x y : X) (d : G)
    (hfix : ∀ z ∈ MulAction.orbit P x, d • z = z)
    (hmove : ∀ z ∈ MulAction.orbit Q y, d • z ≠ z) :
    (MulAction.orbit P x).ncard+(MulAction.orbit Q y).ncard ≤ Nat.card X := by
  have hd : Disjoint (MulAction.orbit P x) (MulAction.orbit Q y) :=
    Set.disjoint_left.mpr (fun z hzP hzQ => hmove z hzQ (hfix z hzP))
  rw [←Set.ncard_union_eq hd]
  exact Set.ncard_le_card _

theorem degree_le_of_two_orbits (P Q : Subgroup G) (c d : G) (a b : ℕ)
    (hc : ∃ x : X, c • x ≠ x) (hd : ∃ y : X, d • y ≠ y)
    (hP : ∀ x : X, c • x ≠ x → a ≤ (MulAction.orbit P x).ncard)
    (hsmall : ∀ x : X, c • x ≠ x → (MulAction.orbit P x).ncard < a+b →
      ∀ z ∈ MulAction.orbit P x, d • z = z)
    (hQ : ∀ y : X, d • y ≠ y → b ≤ (MulAction.orbit Q y).ncard)
    (hmove : ∀ y : X, d • y ≠ y → ∀ z ∈ MulAction.orbit Q y, d • z ≠ z) :
    a+b ≤ Nat.card X := by
  by_contra hh
  have hlt : Nat.card X < a+b := Nat.lt_of_not_ge hh
  obtain ⟨x,hx⟩ := hc
  obtain ⟨y,hy⟩ := hd
  have hpx : (MulAction.orbit P x).ncard < a+b := (Set.ncard_le_card _).trans_lt hlt
  have h := (Nat.add_le_add (hP x hx) (hQ y hy)).trans
    (orbit_card_add_le P Q x y d (hsmall x hx hpx) (hmove y hy))
  exact (Nat.not_lt_of_ge h) hlt

theorem orbit_motion_of_conjugate_eq_or_inverse (Q : Subgroup G) (d : G) (y : X)
    (hy : d • y ≠ y)
    (hconj : ∀ q : Q, (q : G)⁻¹*d*q = d ∨ (q : G)⁻¹*d*q = d⁻¹) :
    ∀ z ∈ MulAction.orbit Q y, d • z ≠ z := by
  intro z hz
  obtain ⟨q,rfl⟩ := hz
  intro he
  change d • ((q : G) • y) = (q : G) • y at he
  have hc : ((q : G)⁻¹*d*q) • y = y := by
    simpa only [mul_smul,inv_smul_smul] using congrArg (fun w : X => (q : G)⁻¹ • w) he
  rcases hconj q with hq|hq
  · rw [hq] at hc
    exact hy hc
  · rw [hq] at hc
    have hi := congrArg (fun w : X => d • w) hc
    exact hy (by simpa only [smul_inv_smul] using hi.symm)

end SymmetricSubgroupAsymptotics.SubgroupOrbitFixedMovedSeparation
