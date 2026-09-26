import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.PGroupNormalIndexP

/-! Finite original-ambient checks for a binary radical chain. An actual
normal section of index two kills both squares and mixed commutators.
A reverse square-generation witness therefore identifies the literal
relative-character radical, with no numerical head premise. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G]

/-- Every original binary relative character radical is contained in an
original ambient-normal subgroup with index two in N. -/
theorem binaryRelativeRadical_le_of_index_two
    (hG : IsPGroup 2 G) (R N : Subgroup G) [R.Normal] [N.Normal]
    (hRN : R ≤ N) (hindex : R.relIndex N=2) :
    primeRelativeRadical 2 N ≤ R := by
  rw [primeRelativeRadical_eq_powerCommutator]
  apply sup_le
  · apply (Subgroup.closure_le R).mpr
    rintro _ ⟨n,rfl⟩
    let q := QuotientGroup.mk' (R.subgroupOf N)
    have hcard : Nat.card (N ⧸ R.subgroupOf N)=2 := hindex
    have hpow := pow_card_eq_one' (x := q n)
    rw [hcard,← map_pow] at hpow
    exact (QuotientGroup.eq_one_iff (N := R.subgroupOf N) (n^2)).mp hpow
  · apply Subgroup.commutator_le.mpr
    intro n hn g _
    let q := QuotientGroup.mk' R
    have hc : q n ∈ Subgroup.center (G ⧸ R) :=
      pGroup_normal_index_p_central hG R N hRN hindex n hn
    apply (QuotientGroup.eq_one_iff (N := R) _).mp
    change q ⁅n, g⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have hcomm : Commute (q g) (q n) := Subgroup.mem_center_iff.mp hc (q g)
    exact hcomm.eq.symm

/-- A literal square-generation certificate supplies the reverse inclusion.
The input is a subgroup containment, not a relative-head or radical premise. -/
theorem binaryRelativeRadical_eq_of_index_two
    (hG : IsPGroup 2 G) (R N : Subgroup G) [R.Normal] [N.Normal]
    (hRN : R ≤ N) (hindex : R.relIndex N=2)
    (hpowers : R ≤ Subgroup.closure (Set.range (fun n : N => (n : G)^2))) :
    primeRelativeRadical 2 N=R := by
  apply le_antisymm (binaryRelativeRadical_le_of_index_two hG R N hRN hindex)
  exact hpowers.trans (le_sup_left.trans (primeRelativePowerCommutator_le_radical 2 N))

/-- Exact order-four/order-two data bind both heads under the whole
original G. The second radical is bottom; no ambient action is changed. -/
theorem binaryRelativeRadical_chain_four_two
    (hG : IsPGroup 2 G) (R N : Subgroup G) [R.Normal] [N.Normal]
    (hRN : R ≤ N) (hN : Nat.card N=4) (hR : Nat.card R=2)
    (hpowers : R ≤ Subgroup.closure (Set.range (fun n : N => (n : G)^2))) :
    primeRelativeRadical 2 N=R ∧ primeRelativeRadical 2 R=⊥ ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=1 ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 R)=1 := by
  have hindex : R.relIndex N=2 := by
    have hm := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) R N bot_le hRN
    rw [Subgroup.relIndex_bot_left,Subgroup.relIndex_bot_left,hR,hN] at hm
    omega
  have hrad := binaryRelativeRadical_eq_of_index_two hG R N hRN hindex hpowers
  have hradR : primeRelativeRadical 2 R=⊥ := by
    apply le_bot_iff.mp
    apply binaryRelativeRadical_le_of_index_two hG ⊥ R bot_le
    simpa only [Subgroup.relIndex_bot_left] using hR
  have hdimN : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=1 := by
    have hc := primeRelativeRadical_card_factorization 2 N
    rw [hN,hrad,hR] at hc
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=2^1
    norm_num only [pow_one]
    omega
  have hdimR : Module.finrank (ZMod 2) (primeRelativeCharacters 2 R)=1 := by
    have hc := primeRelativeRadical_card_factorization 2 R
    rw [hR,hradR,Subgroup.card_bot,mul_one] at hc
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 R)=2^1
    simpa only [pow_one] using hc.symm
  exact ⟨hrad,hradR,hdimN,hdimR⟩

end SymmetricSubgroupAsymptotics
