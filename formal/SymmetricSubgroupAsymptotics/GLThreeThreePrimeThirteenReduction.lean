import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import Mathlib.Data.Nat.GCD.Basic

/-! A generic actual GL3(F3) reduction. All nonsoluble subgroups have
order divisible by thirteen; no irreducibility or subgroup locator is
assumed. Burnside handles the entire complementary part at once. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GLThreeThreePrimeThirteenReduction
open StandardThreeDimensionalLinearGroups

private theorem two_prime_divisor_receipt :
    ∀ n : Fin 865,n.val ∣ 864 →
      ∃ a : Fin 6,∃ b : Fin 4,n.val=2^a.val*3^b.val := by decide +kernel

theorem actual_order_dvd {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f) : Nat.card L ∣ 11232 := by
  simpa only [card_GL_three] using Subgroup.card_dvd_of_injective f hf

theorem isSolvable_of_not_thirteen_dvd {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (h13 : ¬13 ∣ Nat.card L) : IsSolvable L := by
  have hd := actual_order_dvd f hf
  have hc : Nat.Coprime (Nat.card L) 13 :=
    ((show Nat.Prime 13 by decide).coprime_iff_not_dvd.mpr h13).symm
  have hsmall : Nat.card L ∣ 864 := by
    apply hc.dvd_mul_right.mp
    simpa only [show (864 : ℕ)*13=11232 by decide] using hd
  have hle : Nat.card L ≤ 864 := Nat.le_of_dvd (by decide) hsmall
  obtain ⟨a,b,hab⟩ := two_prime_divisor_receipt ⟨Nat.card L,by omega⟩ hsmall
  exact burnsideTwoPrimeSolvability.solvable L 2 3 a.val b.val
    Nat.prime_two Nat.prime_three hab

theorem thirteen_dvd_of_nonsoluble {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (hL : ¬IsSolvable L) : 13 ∣ Nat.card L := by
  by_contra h
  exact hL (isSolvable_of_not_thirteen_dvd f hf h)

end SymmetricSubgroupAsymptotics.GLThreeThreePrimeThirteenReduction
