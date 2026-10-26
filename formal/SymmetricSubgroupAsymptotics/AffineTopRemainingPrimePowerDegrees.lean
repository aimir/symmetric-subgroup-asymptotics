import SymmetricSubgroupAsymptotics.PrimitiveAffineFiniteDegreeSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import Mathlib.Data.Nat.Log

/-! Exact arithmetic exhaustion after the proved large-degree, prime,
and low translation-dimension affine-top ranges. The old prime-power
classification is reused; no groups or actions are enumerated. This
holds for the bare regular p-group profile, without primitivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AffineTopRemainingPrimePowerDegrees

theorem degree_of_uncovered_prime_power (p d n : ℕ) (hp : p.Prime)
    (heq : n=p^d) (hn : 5 ≤ n) (hlarge : ¬128 ≤ n) (hprime : ¬n.Prime)
    (hlow : ¬((49 ≤ n ∧ Nat.log p n ≤ 3) ∨ (64 ≤ n ∧ Nat.log p n ≤ 4))) :
    n=8 ∨ n=9 ∨ n=16 ∨ n=25 ∨ n=27 ∨ n=32 ∨ n=64 := by
  have hn128 : n<128 := by omega
  have hd : 0<d := by
    by_contra h
    have hd0 : d=0 := by omega
    rw [hd0,pow_zero] at heq
    omega
  have hpdvd : p∣n := by
    rw [heq]
    exact dvd_pow_self p hd.ne'
  have hcases := Non2UnipotentPrefixFiniteMenu.primePower_lt343_classification
    hp heq hn (by omega)
  rcases hcases with heven|hprime'|h9|h25|h27|h49|h81|h121|h125|h169|h243|h289
  · have htwo : 2∣p^d := by rw [←heq]; exact even_iff_two_dvd.mp heven
    have hp2 : p=2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow htwo)).symm
    have heq2 : n=2^d := by simpa only [hp2] using heq
    have hh := Non2UnipotentPrefixFiniteMenu.twoPower_lt128_classification heq2 hn hn128
    omega
  · exact (hprime hprime').elim
  · omega
  · omega
  · omega
  · have hp7 : p=7 := Nat.prime_eq_prime_of_dvd_pow (m := 2) hp (by decide)
      (by simpa only [h49,show (7:ℕ)^2=49 by decide] using hpdvd)
    exact (hlow (Or.inl ⟨by omega,by rw [hp7,h49]; decide⟩)).elim
  · have hp3 : p=3 := Nat.prime_eq_prime_of_dvd_pow (m := 4) hp (by decide)
      (by simpa only [h81,show (3:ℕ)^4=81 by decide] using hpdvd)
    exact (hlow (Or.inr ⟨by omega,by rw [hp3,h81]; decide⟩)).elim
  · have hp11 : p=11 := Nat.prime_eq_prime_of_dvd_pow (m := 2) hp (by decide)
      (by simpa only [h121,show (11:ℕ)^2=121 by decide] using hpdvd)
    exact (hlow (Or.inl ⟨by omega,by rw [hp11,h121]; decide⟩)).elim
  · have hp5 : p=5 := Nat.prime_eq_prime_of_dvd_pow (m := 3) hp (by decide)
      (by simpa only [h125,show (5:ℕ)^3=125 by decide] using hpdvd)
    exact (hlow (Or.inl ⟨by omega,by rw [hp5,h125]; decide⟩)).elim
  · omega
  · omega
  · omega

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem degree_of_uncovered_profile (hn : 5 ≤ Nat.card X)
    (hlarge : ¬128 ≤ Nat.card X) (hprime : ¬(Nat.card X).Prime)
    (hlow : ¬((49 ≤ Nat.card X ∧ Nat.log P.p (Nat.card X) ≤ 3) ∨
      (64 ≤ Nat.card X ∧ Nat.log P.p (Nat.card X) ≤ 4))) :
    Nat.card X=8 ∨ Nat.card X=9 ∨ Nat.card X=16 ∨ Nat.card X=25 ∨
      Nat.card X=27 ∨ Nat.card X=32 ∨ Nat.card X=64 := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  obtain ⟨d,hd⟩ := P.V_pgroup.exists_card_eq
  have heq : Nat.card X=P.p^d := (P.card_eq x).symm.trans hd
  exact degree_of_uncovered_prime_power P.p d (Nat.card X) P.p_prime heq hn hlarge hprime hlow

end SymmetricSubgroupAsymptotics.AffineTopRemainingPrimePowerDegrees
