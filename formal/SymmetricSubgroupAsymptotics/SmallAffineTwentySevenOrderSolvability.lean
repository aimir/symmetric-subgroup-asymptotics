import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

/-! Solvability follows from the actual small degree27 complement orders.
The only three-prime order78 has a normal Sylow13 subgroup and quotient6. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem isSolvable_of_card_seventyEight
    {G : Type} [Group G] [Finite G] (hG : Nat.card G=78) : IsSolvable G := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 G := Classical.choice inferInstance
  have hP : Nat.card P=13 := by
    rw [P.card_eq_multiplicity,hG]
    decide +kernel
  have hi : P.index=6 := by
    have hm := (P : Subgroup G).card_mul_index
    rw [hP,hG] at hm
    omega
  have hdiv : Nat.card (Sylow 13 G)∣6 := by
    simpa only [hi] using P.card_dvd_index
  have hle : Nat.card (Sylow 13 G)≤6 := Nat.le_of_dvd (by decide) hdiv
  have hmod := card_sylow_modEq_one 13 G
  change Nat.card (Sylow 13 G)%13=1%13 at hmod
  have hone : Nat.card (Sylow 13 G)=1 := by omega
  letI : Subsingleton (Sylow 13 G) := (Nat.card_eq_one_iff_unique.mp hone).1
  letI : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  letI : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hQ : Nat.card (G⧸(P : Subgroup G))=6 := by rw [←Subgroup.index_eq_card,hi]
  letI : IsSolvable (G⧸(P : Subgroup G)) :=
    burnsideTwoPrimeSolvability.solvable (G⧸(P : Subgroup G)) 2 3 1 1
      Nat.prime_two Nat.prime_three (by simpa only [pow_one] using hQ)
  exact solvable_of_ker_le_range (P : Subgroup G).subtype
    (QuotientGroup.mk' (P : Subgroup G)) (by
      rw [QuotientGroup.ker_mk',Subgroup.range_subtype])

theorem isSolvable_of_small_twentySeven_complement_order
    {G : Type} [Group G] [Finite G]
    (hG : Nat.card G=12 ∨ Nat.card G=13 ∨ Nat.card G=24 ∨
      Nat.card G=26 ∨ Nat.card G=39 ∨ Nat.card G=48 ∨ Nat.card G=78) :
    IsSolvable G := by
  rcases hG with h | h | h | h | h | h | h
  · exact (SmallAffineTwoPrimeOrders.certificate burnsideTwoPrimeSolvability 10 h).solvable
  · exact (SmallAffineTwoPrimeOrders.certificate burnsideTwoPrimeSolvability 11 h).solvable
  · exact (SmallAffineTwoPrimeOrders.certificate burnsideTwoPrimeSolvability 12 h).solvable
  · exact (SmallAffineTwoPrimeOrders.certificate burnsideTwoPrimeSolvability 15 h).solvable
  · exact (SmallAffineTwoPrimeOrders.certificate burnsideTwoPrimeSolvability 16 h).solvable
  · exact (SmallAffineTwoPrimeOrders.certificate burnsideTwoPrimeSolvability 17 h).solvable
  · exact isSolvable_of_card_seventyEight h

end SymmetricSubgroupAsymptotics
