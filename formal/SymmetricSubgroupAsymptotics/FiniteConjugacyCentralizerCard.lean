import SymmetricSubgroupAsymptotics.FiniteConjugacyCardinalCover
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Rank

/-!
# Centralizer input for sparse conjugacy covers

The selected finite emitter checks centralizers in the small block-image and
binary-kernel coordinates.  This file converts those exact centralizer
orders into the class-cardinality sum required by
`FiniteConjugacyCardinalCover`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {c : ℕ}

/-- The subtype defined directly by `IsConj` is the carrier of the
corresponding Mathlib conjugacy class. -/
def isConjSubtypeEquivCarrier (g : G) :
    {x : G // IsConj x g} ≃ (ConjClasses.mk g).carrier :=
  Equiv.subtypeEquivRight (fun x => by
    rw [ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj])

/-- Orbit--stabilizer in the exact form used by the selected finite
certificate. -/
theorem isConj_card_eq_div_centralizer (g : G) :
    Nat.card {x : G // IsConj x g} =
      Nat.card G / Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (ConjAct G) g) := Fintype.ofFinite _
  calc
    Nat.card {x : G // IsConj x g} =
        Nat.card (ConjClasses.mk g).carrier :=
      Nat.card_congr (isConjSubtypeEquivCarrier g)
    _ = Nat.card G /
        Nat.card (MulAction.stabilizer (ConjAct G) g) := by
      simpa only [Nat.card_eq_fintype_card] using
        ConjClasses.card_carrier g
    _ = Nat.card G / Nat.card (Subgroup.centralizer ({g} : Set G)) := by
      rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]

namespace FiniteConjugacyCardinalCover

/-- Exact centralizer orders and one arithmetic class-sum identity supply
the sparse conjugacy cover.  No elementwise coverage function is an input. -/
def ofCentralizerSum (representative : Fin c → G)
    (separated : ∀ i j,
      IsConj (representative i) (representative j) → i = j)
    (class_card_sum :
      (∑ i : Fin c,
          Nat.card G /
            Nat.card (Subgroup.centralizer
              ({representative i} : Set G))) = Nat.card G) :
    FiniteConjugacyCardinalCover representative where
  separated := separated
  class_card_sum := by
    simpa only [isConj_card_eq_div_centralizer] using class_card_sum

end FiniteConjugacyCardinalCover
end SymmetricSubgroupAsymptotics

end
