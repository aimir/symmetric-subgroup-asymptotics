import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.Order.Units
import Mathlib.Algebra.Ring.Parity

/-! A character distinguishes a forbidden ambient conjugator coset from
all original-group conjugators. No ambient extension of automorphisms,
class count, or model recognition is assumed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CharacterConjugacySeparation

theorem character_eq_one_of_odd_card {G : Type*} [Group G] [Finite G]
    (chi : G →* ℤˣ) (hodd : Odd (Nat.card G)) (g : G) : chi g = 1 := by
  have hp : (chi g) ^ Nat.card G = 1 := by
    rw [←map_pow,pow_card_eq_one',map_one]
  rcases Int.units_eq_one_or (chi g) with h | h
  · exact h
  · rw [h,hodd.neg_one_pow] at hp
    exact False.elim ((by decide : (-1 : ℤˣ) ≠ 1) hp)

theorem not_isConj_of_nontrivial_character_coset
    {G H : Type*} [Group G] [Group H]
    (rho : G →* H) (chi : H →* ℤˣ) (a b : G) (sigma : H)
    (hsource : ∀ g, chi (rho g) = 1)
    (hcentral : ∀ c : H, c * rho a = rho a * c → chi c = 1)
    (hconjugate : sigma * rho a * sigma⁻¹ = rho b)
    (hcharacter : chi sigma ≠ 1) : ¬IsConj a b := by
  intro hab
  obtain ⟨g,hg⟩ := isConj_iff.mp hab
  have hg' : rho g * rho a = rho b * rho g := by
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [map_mul,map_inv] using congrArg rho hg
  have hs : sigma⁻¹ * rho b = rho a * sigma⁻¹ := by
    rw [←hconjugate]
    simp only [mul_assoc,inv_mul_cancel_left]
  have hc : (sigma⁻¹ * rho g) * rho a = rho a * (sigma⁻¹ * rho g) := by
    calc
      _ = sigma⁻¹ * (rho g * rho a) := mul_assoc _ _ _
      _ = sigma⁻¹ * (rho b * rho g) := by rw [hg']
      _ = (sigma⁻¹ * rho b) * rho g := (mul_assoc _ _ _).symm
      _ = (rho a * sigma⁻¹) * rho g := by rw [hs]
      _ = _ := mul_assoc _ _ _
  have hc' := hcentral (sigma⁻¹ * rho g) hc
  have hinv : (chi sigma)⁻¹ = 1 := by
    simpa only [map_mul,map_inv,hsource,mul_one] using hc'
  apply hcharacter
  simpa only [inv_inv,inv_one] using congrArg Inv.inv hinv

end SymmetricSubgroupAsymptotics.CharacterConjugacySeparation
