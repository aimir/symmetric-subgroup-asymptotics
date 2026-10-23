import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-! A selected degree-six partition certificate. The explicit antidiagonal
has 462 candidate weighted count vectors, and the divisibility filter
retains exactly actual positive-part multiplicities. The predicates and
both cardinalities are evaluated by the Lean kernel; no external table
or producer supplies a mathematical premise. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.AlternatingSixPartitionCapacity

def weightedMenu : Finset (ℕ →₀ ℕ) :=
  ((Finset.Icc 1 6).finsuppAntidiag 6).filter
    (fun f => ∀ i : Fin 6, i.val + 1 ∣ f (i.val + 1))

def decodedCard (f : ℕ →₀ ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 6, f i / i

def evenMenu : Finset (ℕ →₀ ℕ) :=
  weightedMenu.filter (fun f => Even (6 + decodedCard f))

def splitMenu : Finset (ℕ →₀ ℕ) :=
  weightedMenu.filter (fun f =>
    (∀ i : Fin 6, f (i.val + 1) / (i.val + 1) ≤ 1) ∧
    (∀ i : Fin 6, Even (i.val + 1) → f (i.val + 1) = 0))

theorem evenMenu_card : evenMenu.card = 6 := by decide +kernel

theorem splitMenu_card : splitMenu.card = 1 := by decide +kernel

end SymmetricSubgroupAsymptotics.AlternatingSixPartitionCapacity
