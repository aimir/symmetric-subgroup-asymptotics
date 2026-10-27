import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import Mathlib.GroupTheory.Nilpotent

/-! This adapter isolates the sole use of odd-order solvability. On the
common Axiom69 toolchain its argument is supplied by the actual theorem
CFSG.FeitThompson.isSolvable_of_odd_natCard, independently of a classification
into old carriers. No such input is added to a public T1 endpoint here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SylowTwoNormalizerOfOddOrderSolvability
open CFSGReduction

def OddOrderSolvability : Prop :=
  ∀ (G : Type) [Group G] [Finite G],Odd (Nat.card G) → IsSolvable G

theorem normalizer_quotient_odd {G : Type} [Group G] [Finite G] (P : Sylow 2 G) :
    Odd (Nat.card ((Subgroup.normalizer (P : Set G))⧸
      (P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G)))) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := P.subtype (Subgroup.le_normalizer :
    (P : Subgroup G)≤Subgroup.normalizer (P : Set G))
  apply Nat.not_even_iff_odd.mp
  intro heven
  apply Q.not_dvd_index
  rw [Subgroup.index_eq_card]
  exact even_iff_two_dvd.mp heven

theorem normalizer_solvable (hodd : OddOrderSolvability)
    {G : Type} [Group G] [Finite G] (P : Sylow 2 G) :
    IsSolvable (Subgroup.normalizer (P : Set G)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let Q : Sylow 2 N := P.subtype Subgroup.le_normalizer
  let S : Subgroup N := Q
  letI : S.Normal := by
    change ((P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G))).Normal
    exact (P : Subgroup G).normal_in_normalizer
  letI : Group.IsNilpotent S := Q.isPGroup'.isNilpotent
  letI : IsSolvable S := inferInstance
  letI : IsSolvable (N⧸S) := hodd (N⧸S) (normalizer_quotient_odd P)
  exact solvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
    (le_of_eq (by rw [QuotientGroup.ker_mk',Subgroup.range_subtype]))

theorem goodSylowTwo_of_two_binary_subgroups (hodd : OddOrderSolvability)
    {G : Type} [Group G] [Finite G]
    (U V : Subgroup G) (hU : IsPGroup 2 U) (hV : IsPGroup 2 V)
    (hgen : U⊔V=⊤) : GoodSylowPrime G 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    U V hU hV hgen ⟨default,normalizer_solvable hodd default⟩

end SymmetricSubgroupAsymptotics.SylowTwoNormalizerOfOddOrderSolvability
