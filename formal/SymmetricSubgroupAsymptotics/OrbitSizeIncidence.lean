import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Point budgets for marked original orbits

The literal points of selected actual orbits inject into the original
point set. Thus marking an orbit of size at least d has at most |X|/d
choices. The selected predicate is arbitrary and need not classify the
other orbit actions. This applies both to pair pointing and E8 pointing.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.OrbitSizeIncidence

variable {G X : Type*} [Group G] [MulAction G X]
    (P : MulAction.orbitRel.Quotient G X → Prop)

abbrev Selected := {o : MulAction.orbitRel.Quotient G X // P o}

def point (z : Σ o : Selected P, o.val.orbit) : X := z.2.val

theorem point_injective : Function.Injective (point P) := by
  rintro ⟨o,x⟩ ⟨p,y⟩ h
  have hxy : (x : X) = (y : X) := h
  have hq := congrArg (Quotient.mk (MulAction.orbitRel G X)) hxy
  have hop : o = p := Subtype.ext
    ((MulAction.orbitRel.Quotient.mem_orbit.mp x.property).symm.trans
      (hq.trans (MulAction.orbitRel.Quotient.mem_orbit.mp y.property)))
  subst p
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Exact original orbit sizes are charged to disjoint original points. -/
theorem sum_orbit_card_le [Finite X] :
    (∑ o : Selected P, Nat.card o.val.orbit) ≤ Nat.card X := by
  have h := Nat.card_le_card_of_injective (point P) (point_injective P)
  simpa only [Nat.card_sigma] using h

/-- An arbitrary selection of actual orbits consumes its full point cost.
No transitivity or product assumption about the original group is used. -/
theorem cardinal_mul_size_le [Finite X] (d : ℕ)
    (hsize : ∀ o : Selected P, d ≤ Nat.card o.val.orbit) :
    Nat.card (Selected P) * d ≤ Nat.card X := by
  calc
    Nat.card (Selected P) * d = ∑ _o : Selected P, d := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ o : Selected P, Nat.card o.val.orbit := by
      exact Finset.sum_le_sum (fun o _ => hsize o)
    _ ≤ Nat.card X := sum_orbit_card_le P

theorem cardinal_le_div_size [Finite X] (d : ℕ) (hd : 0 < d)
    (hsize : ∀ o : Selected P, d ≤ Nat.card o.val.orbit) :
    Nat.card (Selected P) ≤ Nat.card X / d :=
  (Nat.le_div_iff_mul_le hd).mpr (cardinal_mul_size_le P d hsize)

end SymmetricSubgroupAsymptotics.OrbitSizeIncidence
