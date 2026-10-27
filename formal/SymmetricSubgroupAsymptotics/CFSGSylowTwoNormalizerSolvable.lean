import SymmetricSubgroupAsymptotics.CFSGOddOrderSolvabilityComplete
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import Mathlib.GroupTheory.Nilpotent

/-! Classification now supplies the odd quotient in every finite Sylow-two
normalizer. Two generating binary subgroups then suffice for GoodSylowPrime;
the generation condition is retained explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

variable {G : Type} [Group G] [Finite G]

/-- The normalizer quotient by its Sylow-two subgroup has odd order. -/
theorem sylow_two_normalizer_quotient_odd (P : Sylow 2 G) :
    Odd (Nat.card ((Subgroup.normalizer (P : Set G)) ⧸
      (P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G)))) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := P.subtype (Subgroup.le_normalizer :
    (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G))
  apply Nat.not_even_iff_odd.mp
  intro heven
  apply Q.not_dvd_index
  rw [Subgroup.index_eq_card]
  exact even_iff_two_dvd.mp heven

/-- This holds for every Sylow-two subgroup, without a simple-group premise. -/
theorem sylow_two_normalizer_isSolvable (hCFSG : CFSG.CFSGClassification)
    (P : Sylow 2 G) : IsSolvable (Subgroup.normalizer (P : Set G)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let Q : Sylow 2 N := P.subtype Subgroup.le_normalizer
  let S : Subgroup N := Q
  letI : S.Normal := by
    change ((P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G))).Normal
    exact (P : Subgroup G).normal_in_normalizer
  letI : Group.IsNilpotent S := Q.isPGroup'.isNilpotent
  letI : IsSolvable S := inferInstance
  letI : IsSolvable (N ⧸ S) :=
    odd_order_solvable_of_cfsg hCFSG (N ⧸ S) (sylow_two_normalizer_quotient_odd P)
  exact solvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
    (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-- The only remaining group-specific input is generation by two binary
subgroups; they need not themselves be Sylow subgroups. -/
theorem goodSylowTwo_of_two_binary_subgroups (hCFSG : CFSG.CFSGClassification)
    (U V : Subgroup G) (hU : IsPGroup 2 U) (hV : IsPGroup 2 V)
    (hgen : U ⊔ V = ⊤) : GoodSylowPrime G 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    U V hU hV hgen ⟨default, sylow_two_normalizer_isSolvable hCFSG default⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
