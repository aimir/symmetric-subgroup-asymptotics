import SymmetricSubgroupAsymptotics.NonabelianSimpleOrderAtLeastSixty
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! Raw actual degree forms force one socle factor below degree25.
Product-action indices are at least5; diagonal degrees are at least60.
No global simple-index-square packet, outer estimate or faithful action
bound is needed beyond the exact raw NonaffineData fields. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput
open PrimitiveSocleRawStructure

theorem factorCount_eq_one {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X) (hdegree : Nat.card X<25) :
    D.factorCount=1 := by
  have hpos := D.factorCount_pos
  by_contra hh
  have hk : 2≤D.factorCount := by omega
  rcases D.indexForm with ⟨H,hH,heq⟩ | ⟨a,hka,heq⟩
  · have hi := nonabelianSimple_proper_index_five_le
      (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) H hH
    have hl : 25≤H.index ^ D.factorCount := calc
      25=5^2 := by decide
      _ ≤ H.index ^ 2 := Nat.pow_le_pow_left hi 2
      _ ≤ H.index ^ D.factorCount := pow_le_pow_right₀ (by omega) hk
    rw [←heq] at hl
    omega
  · have hT := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
    have ha : 1≤a := by omega
    have hl : 60≤Nat.card X := calc
      60≤Nat.card D.Simple := hT
      _=Nat.card D.Simple ^ 1 := (pow_one _).symm
      _≤Nat.card D.Simple ^ a := pow_le_pow_right₀ (by omega) ha
      _=Nat.card X := heq.symm
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput
