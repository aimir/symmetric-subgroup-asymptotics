import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCharTwoQuantitative

/-! The actual elementary D centre has order prime to the defining
characteristic, including characteristic two where it is trivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterPrimeCoprime
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDCenterCardinality

theorem center_prime_coprime (K : Type) [Field K] [Finite K]
    (s p : ℕ) [Fact p.Prime] [CharP K p] :
    p.Coprime (Nat.card (Subgroup.center (elementaryRootGroup K (s + 4)))) := by
  by_cases hp : p = 2
  · subst p
    rw [CFSGOrthogonalDCharTwoQuantitative.center_eq_bot K s, Subgroup.card_bot]
    exact Nat.coprime_one_right _
  · apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hdiv
    have hpos : 0 < Nat.card (Subgroup.center (elementaryRootGroup K (s + 4))) := Nat.card_pos
    have hle := Nat.le_of_dvd hpos hdiv
    have htwo := center_card_le_two K s
    have hp2 := (Fact.out : p.Prime).two_le
    exact hp (by omega)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterPrimeCoprime
