import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-! A concrete polynomial code for normal-tableau rows.
A monotone chain in a fixed finite partial order is recovered from the
cardinalities of its lower-level sets. This avoids assuming a tableau menu
bound or counting arbitrary arrays at a quadratic entropy cost. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.FiniteMonotoneChainCount

variable (n : ℕ) (P : Type) [Fintype P] [PartialOrder P]
abbrev Chain := {f : Fin n → P // Monotone f}

def below (f : Chain n P) (x : P) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f.val i≤x)

def code (f : Chain n P) : P → Fin (n+1) := fun x =>
  ⟨(below n P f x).card,Nat.lt_succ_of_le
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin n))⟩

/-- The count of lower-level sets determines every original chain value. -/
theorem code_injective : Function.Injective (code n P) := by
  intro f g he
  have hle (a d : Chain n P) (had : code n P a=code n P d) : ∀ j,a.val j≤d.val j := by
    intro j
    by_contra hj
    have hsub : below n P a (d.val j) ⊆ Finset.Iio j := by
      intro i hi
      have hix : a.val i≤d.val j := (Finset.mem_filter.mp hi).2
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact hj ((a.property (le_of_not_gt hji)).trans hix)
    have hsub' : Finset.Iic j ⊆ below n P d (d.val j) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,d.property (Finset.mem_Iic.mp hi)⟩
    have ha := Finset.card_le_card hsub
    have hd := Finset.card_le_card hsub'
    have hc := congrArg (fun q : P → Fin (n+1) => (q (d.val j)).val) had
    change (below n P a (d.val j)).card=(below n P d (d.val j)).card at hc
    rw [Fin.card_Iio] at ha
    rw [Fin.card_Iic] at hd
    omega
  apply Subtype.ext
  funext j
  exact le_antisymm (hle f g he j) (hle g f he.symm j)

/-- Each tableau row has polynomially many possibilities in its length,
with exponent depending only on the fixed finite normal-subgroup menu. -/
theorem card_chain_le : Fintype.card (Chain n P) ≤ (n+1)^Fintype.card P := by
  have h := Fintype.card_le_of_injective (code n P) (code_injective n P)
  simpa only [Fintype.card_fun,Fintype.card_fin] using h

end SymmetricSubgroupAsymptotics.MarkedC4.FiniteMonotoneChainCount
