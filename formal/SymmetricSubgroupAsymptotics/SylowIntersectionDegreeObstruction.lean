import SymmetricSubgroupAsymptotics.SylowIntersectionOrbitDivisibility
import SymmetricSubgroupAsymptotics.SylowFixedPointNormalizerOrbit
import SymmetricSubgroupAsymptotics.FiniteActionOrbitMultipleFixedCongruence
import Mathlib.Data.Nat.Prime.Basic

/-! Actual Sylow intersection indices control the degree of the SAME
transitive action. A fixed-point count is both a divisor of the actual
normalizer/Sylow relative index and congruent to the action degree.
The final small arithmetic obstruction uses only divisors of 7 squared. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SylowIntersectionDegreeObstruction
open MulAction

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [IsPretransitive G X] [Finite X]

theorem exists_fixed_card_dvd_and_modEq (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (q : ℕ) (hq : 2≤q)
    (hintersection : ∀ g : G,
      (P : Subgroup G) ⊓ ((g • P : Sylow p G) : Subgroup G) ≠ (P : Subgroup G) →
      q ∣ ((P : Subgroup G) ⊓ ((g • P : Sylow p G) : Subgroup G)).relIndex
        (P : Subgroup G))
    (hdegree : ¬p ∣ Nat.card X) :
    ∃ d : ℕ, 0<d ∧
      d ∣ (P : Subgroup G).relIndex (Subgroup.normalizer (P : Set G)) ∧
      Nat.ModEq q (Nat.card X) d := by
  obtain ⟨x,hx⟩ := P.2.nonempty_fixed_point_of_prime_not_dvd_card X hdegree
  letI : Nonempty (fixedPoints P X) := ⟨⟨x,hx⟩⟩
  refine ⟨Nat.card (fixedPoints P X),Nat.card_pos,?_,?_⟩
  · exact SylowFixedPointNormalizerOrbit.fixed_card_dvd_normalizer_relIndex p P x hx
  · exact FiniteActionOrbitMultipleFixedCongruence.card_modEq_card_fixedPoints q hq
      (fun y hy => SylowIntersectionOrbitDivisibility.dvd_orbit_card_of_not_fixed
        p P q hintersection x hx y hy)

theorem not_modEq_oneOhNine_of_dvd_fortyNine (d : ℕ) (hd : d∣49) :
    ¬Nat.ModEq 8 109 d := by
  have hd' : d∣7^2 := hd
  obtain ⟨k,hk,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hd'
  interval_cases k <;> norm_num [Nat.ModEq] at *

theorem card_ne_oneOhNine_of_eight_and_fortyNine [Fact (Nat.Prime 2)]
    (P : Sylow 2 G)
    (hintersection : ∀ g : G,
      (P : Subgroup G) ⊓ ((g • P : Sylow 2 G) : Subgroup G) ≠ (P : Subgroup G) →
      8 ∣ ((P : Subgroup G) ⊓ ((g • P : Sylow 2 G) : Subgroup G)).relIndex
        (P : Subgroup G))
    (hnormalizer : (P : Subgroup G).relIndex
      (Subgroup.normalizer (P : Set G))=49) : Nat.card X≠109 := by
  intro hdegree
  obtain ⟨d,hdpos,hd,hmod⟩ := exists_fixed_card_dvd_and_modEq
    (X:=X) 2 P 8 (by decide) hintersection (by rw [hdegree]; norm_num)
  rw [hnormalizer] at hd
  rw [hdegree] at hmod
  exact not_modEq_oneOhNine_of_dvd_fortyNine d hd hmod

end SymmetricSubgroupAsymptotics.SylowIntersectionDegreeObstruction
