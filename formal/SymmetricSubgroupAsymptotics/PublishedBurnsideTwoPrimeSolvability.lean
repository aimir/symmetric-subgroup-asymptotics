import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FinCases

/-! Burnside's classical p^a q^b theorem is retained as a group-uniform
published input, independently of any finite catalogue or capacity bound.
The displayed eighteen orders are numerical witnesses only: applying the
factory still requires an actual group's exact cardinality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure PublishedBurnsideTwoPrimeSolvabilityInput where
  solvable : ∀ (G : Type) [Group G] [Finite G] (p q a b : ℕ),
    Nat.Prime p → Nat.Prime q → Nat.card G=p^a*q^b → IsSolvable G

structure FiniteSolvableOrderCertificate (G : Type) [Group G] [Finite G] (order : ℕ) where
  card_eq : Nat.card G=order
  solvable : IsSolvable G

namespace SmallAffineTwoPrimeOrders

def order : Fin 18 → ℕ := ![7,21,5,10,15,18,20,36,36,72,12,13,24,24,24,26,39,48]
def p : Fin 18 → ℕ := ![7,3,5,2,3,2,2,2,2,2,2,13,2,2,2,2,3,2]
def q : Fin 18 → ℕ := ![7,7,5,5,5,3,5,3,3,3,3,13,3,3,3,13,13,3]
def a : Fin 18 → ℕ := ![1,1,1,1,1,1,2,2,2,3,2,1,3,3,3,1,1,4]
def b : Fin 18 → ℕ := ![0,1,0,1,1,2,1,2,2,2,1,0,1,1,1,1,1,1]
theorem specification (i : Fin 18) :
    Nat.Prime (p i) ∧ Nat.Prime (q i) ∧ order i=(p i)^(a i)*(q i)^(b i) := by
  fin_cases i <;> decide +kernel

def certificate (B : PublishedBurnsideTwoPrimeSolvabilityInput)
    {G : Type} [Group G] [Finite G] (i : Fin 18) (hcard : Nat.card G=order i) :
    FiniteSolvableOrderCertificate G (order i) where
  card_eq := hcard
  solvable := B.solvable G (p i) (q i) (a i) (b i)
    (specification i).1 (specification i).2.1 (hcard.trans (specification i).2.2)

end SmallAffineTwoPrimeOrders
end SymmetricSubgroupAsymptotics
