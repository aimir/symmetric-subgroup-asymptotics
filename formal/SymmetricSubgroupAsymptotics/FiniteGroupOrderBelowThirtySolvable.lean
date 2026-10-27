import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import Mathlib.GroupTheory.Solvable

/-! A small arithmetic menu, not a group catalogue. Every positive integer
below thirty has at most two prime factors, counted without multiplicity.
Burnside therefore excludes all such orders for nonabelian simple groups. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FiniteGroupOrderBelowThirtySolvable

private def primeOne : Fin 30 → ℕ :=
  ![2,2,2,3,2,5,2,7,2,3,2,11,2,13,2,3,2,17,2,19,2,3,2,23,2,5,2,3,2,29]
private def primeTwo : Fin 30 → ℕ :=
  ![2,2,2,3,2,5,3,7,2,3,5,11,3,13,7,5,2,17,3,19,5,7,11,23,3,5,13,3,7,29]
private def exponentOne : Fin 30 → ℕ :=
  ![0,0,1,1,2,1,1,1,3,2,1,1,2,1,1,1,4,1,1,1,2,1,1,1,3,2,1,3,2,1]
private def exponentTwo : Fin 30 → ℕ :=
  ![0,0,0,0,0,0,1,0,0,0,1,0,1,0,1,1,0,0,2,0,1,1,1,0,1,0,1,0,1,0]

private theorem specification : ∀ i : Fin 30, 0 < i.val →
    (primeOne i).Prime ∧ (primeTwo i).Prime ∧
      i.val=primeOne i ^ exponentOne i * primeTwo i ^ exponentTwo i := by
  decide +kernel

theorem isSolvable_of_card_lt_thirty (G : Type) [Group G] [Finite G]
    (hcard : Nat.card G<30) : IsSolvable G := by
  let i : Fin 30 := ⟨Nat.card G,hcard⟩
  have hs := specification i (show 0 < Nat.card G from Nat.card_pos)
  exact burnsideTwoPrimeSolvability.solvable G (primeOne i) (primeTwo i)
    (exponentOne i) (exponentTwo i) hs.1 hs.2.1 hs.2.2

theorem thirty_le_card_of_nonabelian_simple (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hn : ¬IsMulCommutative G) : 30≤Nat.card G := by
  by_contra hh
  letI : IsSolvable G := isSolvable_of_card_lt_thirty G (by omega)
  exact hn (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))

end SymmetricSubgroupAsymptotics.FiniteGroupOrderBelowThirtySolvable
