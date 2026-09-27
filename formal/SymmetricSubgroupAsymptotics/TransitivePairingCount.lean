import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting original equivariant pairings

A pairing is its actual partner function on the original point set. It
contains no pair labels, orientations, coordinate charts, or witnesses of
their construction. On a nonempty transitive set this function is
determined by the partner of one fixed original point.

The point or nonemptiness hypothesis matters: the empty set has one empty
partner function, whereas its cardinality minus one is zero.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A fixed-point-free involution commuting with the given original action.
Only the function is data; all conditions are propositions. -/
def EquivariantPairing (G X : Type*) [Group G] [MulAction G X] :=
  {f : X → X // Function.Involutive f ∧
    (∀ x, f x ≠ x) ∧ ∀ (g : G) x, f (g • x) = g • f x}

namespace EquivariantPairing

variable {G X : Type*} [Group G] [MulAction G X]

/-- Evaluation retains the actual partner and rules out the fixed point. -/
def partner (x : X) (f : EquivariantPairing G X) : {y : X // y ≠ x} :=
  ⟨f.1 x, f.2.2.1 x⟩

/-- Transitivity propagates equality at one original point to equality of
the whole original partner functions. No faithful action is required. -/
theorem partner_injective [MulAction.IsPretransitive G X] (x : X) :
    Function.Injective (partner (G := G) x) := by
  intro f f' h
  have hx : f.1 x = f'.1 x := congrArg Subtype.val h
  apply Subtype.ext
  funext y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  calc
    f.1 (g • x) = g • f.1 x := f.2.2.2 g x
    _ = g • f'.1 x := congrArg (fun z : X => g • z) hx
    _ = f'.1 (g • x) := (f'.2.2.2 g x).symm

/-- There are at most one fewer original pairings than original points.
The codomain of the injection is exactly the complement of the fixed
point, so there is no chart or labelling multiplicity. -/
theorem card_le [Finite X] [MulAction.IsPretransitive G X] (x : X) :
    Nat.card (EquivariantPairing G X) ≤ Nat.card X - 1 := by
  classical
  have hcard : Nat.card {y : X // y ≠ x} = Nat.card X - 1 := by
    letI := Fintype.ofFinite X
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  exact (Nat.card_le_card_of_injective (partner (G := G) x)
    (partner_injective x)).trans_eq hcard

/-- The same bound without choosing a point in the statement. -/
theorem card_le_of_nonempty [Finite X] [Nonempty X]
    [MulAction.IsPretransitive G X] :
    Nat.card (EquivariantPairing G X) ≤ Nat.card X - 1 :=
  card_le (Classical.choice (inferInstance : Nonempty X))

end EquivariantPairing
end SymmetricSubgroupAsymptotics

end
