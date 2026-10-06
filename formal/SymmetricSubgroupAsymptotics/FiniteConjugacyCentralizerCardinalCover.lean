import SymmetricSubgroupAsymptotics.FiniteConjugacyCardinalCover
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Rank

/-!
# Sparse conjugacy coverage from centralizer orders

For small executable row groups, a generated certificate can check the
literal cardinality of each selected centralizer and let orbit-stabilizer
derive the corresponding conjugacy-class cardinality.  This avoids the
larger reversible coordinate charts used by action-level centralizer
certificates when no further centralizer structure is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {c : ℕ}

/-- Pairwise nonconjugate representatives with checked literal centralizer
orders and an exact class-size exhaustion. -/
structure FiniteConjugacyCentralizerCardinalCover
    (representative : Fin c → G) : Type where
  separated : ∀ i j, IsConj (representative i) (representative j) → i = j
  centralizerCard : Fin c → ℕ
  centralizer_card : ∀ i,
    Nat.card (Subgroup.centralizer ({representative i} : Set G)) =
      centralizerCard i
  class_card_sum :
    (∑ i : Fin c, Nat.card G / centralizerCard i) = Nat.card G

namespace FiniteConjugacyCentralizerCardinalCover

variable {representative : Fin c → G}
  (C : FiniteConjugacyCentralizerCardinalCover representative)

include C

/-- The checked centralizer order gives the cardinality of the literal
conjugacy class. -/
theorem class_card (i : Fin c) :
    Nat.card {x : G // IsConj x (representative i)} =
      Nat.card G / C.centralizerCard i := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (MulAction.orbit (ConjAct G) (representative i)) :=
    Fintype.ofFinite _
  letI : Fintype
      (MulAction.stabilizer (ConjAct G) (representative i)) :=
    Fintype.ofFinite _
  let e : MulAction.orbit (ConjAct G) (representative i) ≃
      {x : G // IsConj x (representative i)} :=
    { toFun := fun x ↦ ⟨x, ConjAct.mem_orbit_conjAct.mp x.property⟩
      invFun := fun x ↦ ⟨x, ConjAct.mem_orbit_conjAct.mpr x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hmul :
      Nat.card {x : G // IsConj x (representative i)} *
          Nat.card (MulAction.stabilizer (ConjAct G) (representative i)) =
        Nat.card G := by
    rw [← Nat.card_congr e]
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct G) (representative i)
  have hstabilizer :
      Nat.card (MulAction.stabilizer (ConjAct G) (representative i)) =
        C.centralizerCard i :=
    (Subgroup.nat_card_centralizer_nat_card_stabilizer
      (representative i)).symm.trans (C.centralizer_card i)
  rw [hstabilizer] at hmul
  exact Nat.eq_div_of_mul_eq_left
    (by
      rw [← hstabilizer]
      exact (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩).ne')
    hmul

/-- Forget the checked centralizer orders after deriving the literal class
cardinalities. -/
def toCardinalCover : FiniteConjugacyCardinalCover representative where
  separated := C.separated
  class_card_sum := by
    simpa only [C.class_card] using C.class_card_sum

end FiniteConjugacyCentralizerCardinalCover
end SymmetricSubgroupAsymptotics

end
