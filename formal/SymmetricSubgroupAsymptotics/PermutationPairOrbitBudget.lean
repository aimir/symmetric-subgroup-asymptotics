import SymmetricSubgroupAsymptotics.PermutationPairOrbitMarks

/-!
# The point budget for actual pair orbits

The actual two-point orbits of a permutation subgroup are disjoint subsets
of the original point set.  This file records the resulting sharp bound
without choosing orbit representatives or an orbit-profile presentation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationPairOrbitBudget

open PermutationPairOrbitMarks

variable {X : Type*} [Finite X] (H : Subgroup (Equiv.Perm X))

/-- The disjoint union of the literal points in all actual pair orbits. -/
abbrev PairPoints := Σ s : PairOrbit H, s.val

def point (z : PairPoints H) : X := z.2.val

theorem point_injective : Function.Injective (point H) := by
  rintro ⟨s,x⟩ ⟨t,y⟩ hxy
  have hxy' : (x : X) = (y : X) := hxy
  obtain ⟨a,ha⟩ := s.property.1
  obtain ⟨b,hb⟩ := t.property.1
  have hsa : s.val = MulAction.orbit H a := ha
  have htb : t.val = MulAction.orbit H b := hb
  have hxa : (x : X) ∈ MulAction.orbit H a := by simpa only [← hsa] using x.property
  have hyb : (y : X) ∈ MulAction.orbit H b := by simpa only [← htb] using y.property
  have hax : MulAction.orbit H a = MulAction.orbit H (x : X) :=
    MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit_symm.mp hxa)
  have hby : MulAction.orbit H b = MulAction.orbit H (y : X) :=
    MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit_symm.mp hyb)
  have hstVal : s.val = t.val := by
    rw [hsa,htb,hax,hby,hxy']
  have hst : s = t := Subtype.ext hstVal
  subst t
  have hxySub : x = y := Subtype.ext hxy'
  subst y
  rfl

theorem pairPoints_card : Nat.card (PairPoints H) = Nat.card (PairOrbit H) * 2 := by
  rw [Nat.card_sigma]
  calc
    (∑ s : PairOrbit H, Nat.card s.val) = ∑ _s : PairOrbit H, 2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact s.property.2
    _ = Nat.card (PairOrbit H) * 2 := by
      simp [Nat.card_eq_fintype_card]

/-- Two original points are charged for every actual pair orbit. -/
theorem pairOrbit_card_mul_two_le : Nat.card (PairOrbit H) * 2 ≤ Nat.card X := by
  rw [← pairPoints_card H]
  exact Nat.card_le_card_of_injective (point H) (point_injective H)

theorem pairOrbit_card_le_half : Nat.card (PairOrbit H) ≤ Nat.card X / 2 :=
  (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (pairOrbit_card_mul_two_le H)

theorem pairOrbit_card_fin_le (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N)))) : Nat.card (PairOrbit H) ≤ N := by
  simpa using pairOrbit_card_le_half H

end SymmetricSubgroupAsymptotics.PermutationPairOrbitBudget

