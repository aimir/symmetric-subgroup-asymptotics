import SymmetricSubgroupAsymptotics.PGroupOriginalSocleRelativeHeads
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Every nonabelian group of order8 has cyclic centre of order at most2.
Its actual p-group socle lies in that centre and therefore has one normal
generator. No D8/Q8 model identification or representation matrix is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
local instance nonabelianEightPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem nonabelian_cardEight_center_card_le_two
    {G : Type} [Group G] [Finite G] (hG : Nat.card G=8)
    (hnc : ¬IsMulCommutative G) : Nat.card (Subgroup.center G)≤2 := by
  by_contra h
  have h3 : 3≤Nat.card (Subgroup.center G) := by omega
  have hm := Nat.mul_le_mul_right (Subgroup.center G).index h3
  rw [(Subgroup.center G).card_mul_index,hG] at hm
  have hi : (Subgroup.center G).index≤2 := by omega
  have hp : 0<(Subgroup.center G).index := by
    rw [(Subgroup.center G).index_eq_card]
    exact Nat.card_pos
  have hd : (Subgroup.center G).index∣2 := by
    have hc : (Subgroup.center G).index=1 ∨ (Subgroup.center G).index=2 := by omega
    rcases hc with hc|hc <;> rw [hc] <;> decide
  letI : IsCyclic (G⧸Subgroup.center G) := isCyclic_of_card_dvd_prime (p := 2) (by
    simpa only [Subgroup.index_eq_card] using hd)
  apply hnc
  exact IsMulCommutative.of_comm (commutative_of_cyclic_center_quotient
    (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.ker_mk' _).le)

theorem socleNormalGeneratorBound_one_of_nonabelian_cardEight
    {G : Type} [Group G] [Finite G] (hG : Nat.card G=8)
    (hnc : ¬IsMulCommutative G) : SocleNormalGeneratorBound G 1 := by
  have hc := nonabelian_cardEight_center_card_le_two hG hnc
  have hp : 0<Nat.card (Subgroup.center G) := Nat.card_pos
  have hd : Nat.card (Subgroup.center G)∣2 := by
    have hh : Nat.card (Subgroup.center G)=1 ∨ Nat.card (Subgroup.center G)=2 := by omega
    rcases hh with hh|hh <;> rw [hh] <;> decide
  letI : IsCyclic (Subgroup.center G) := isCyclic_of_card_dvd_prime hd
  have hP : IsPGroup 2 G := IsPGroup.of_card (n := 3) (by simpa using hG)
  have hle : finiteGroupSocle G≤Subgroup.center G := by
    rw [PGroupOriginalSocleRelativeHeads.socle_eq_centralPrimeSoclePart 2 hP]
    exact centralPrimeSoclePart_le_center 2
  letI : IsCyclic (finiteGroupSocle G) := Subgroup.isCyclic_of_le hle
  exact (socleNormalGeneratorBound_iff_normalGen_le G 1).2
    (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic (finiteGroupSocle G))

end SymmetricSubgroupAsymptotics
