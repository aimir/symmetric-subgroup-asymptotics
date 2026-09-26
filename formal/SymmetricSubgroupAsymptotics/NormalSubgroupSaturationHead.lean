import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCommutators
import SymmetricSubgroupAsymptotics.PrimeNormalHeadOrder

/-! A finite nonempty-commutator saturation certificate gives a head
bound for every original ambient-normal subgroup inside D. Subgroups
below R use R's order budget; all others have R inside their actual
relative radical, so the same cardinal budget cancels a factor |R|.
No list of normal subgroups or numerical head premise is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCertificate

variable (p : ℕ) [Fact p.Prime]
    {G ι κ : Type*} [Group G] [Finite G]
    {D R : Subgroup G} {ambient : ι → G} {radicalGenerators : κ → G} {n : ℕ}
    (C : NormalSubgroupSaturationCertificate D R ambient radicalGenerators n)

/-- The complete maximum over original normal subgroups follows from
the actual nonempty words and two subgroup-order bounds. -/
theorem primeNormalHeadMax_le (hne : C.NonemptyWords) (r : ℕ)
    (hsmall : Nat.card R ≤ p ^ r)
    (hlarge : Nat.card D ≤ p ^ r * Nat.card R) :
    primeNormalHeadMax p D ≤ r := by
  apply (SymmetricSubgroupAsymptotics.primeNormalHeadMax_le_iff p D r).mpr
  intro B _ hBD
  by_cases hBR : B ≤ R
  · have hhead := primeRelativeHead_le_normalHeadMax p R B hBR
    have hp : p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) ≤ p ^ r :=
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hhead).trans
        ((primeNormalHeadMax_pow_le_card p R).trans hsmall)
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hp
  · have hrad : R ≤ primeRelativeRadical p B :=
      (C.radical_le_commutator hne B hBD hBR).trans
        ((primeRelativePowerCommutator_commutator_le p B).trans
          (primeRelativePowerCommutator_le_radical p B))
    have hbudget :
        p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) * Nat.card R ≤
          p ^ r * Nat.card R := by
      calc
        _ ≤ p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) *
            Nat.card (primeRelativeRadical p B) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrad)
        _ = Nat.card B := (primeRelativeRadical_card_factorization p B).symm
        _ ≤ Nat.card D := Subgroup.card_le_of_le hBD
        _ ≤ _ := hlarge
    have hp : p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) ≤ p ^ r :=
      Nat.le_of_mul_le_mul_right hbudget (Nat.card_pos (α := R))
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hp

end SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCertificate
