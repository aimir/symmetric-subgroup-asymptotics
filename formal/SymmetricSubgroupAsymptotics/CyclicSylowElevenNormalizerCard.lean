import SymmetricSubgroupAsymptotics.FiniteNormalizerCardDivisor
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Divisors

/-! A cyclic Sylow eleven subgroup in an actual group of order443520.
An ambient centralizer divisor242 and Sylow's congruence determine its
normalizer and centralizer orders. The finite scalar certificate ranges
only over integer divisors of220, not group elements or subgroup classes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicSylowElevenNormalizerCard

private theorem divisor_receipt :
    ∀ n ∈ Nat.divisors 220, (443520 / n) % 11 = 1 → n = 55 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem normalizer_card_eq_fiftyFive (P : Sylow 11 G)
    (hG : Nat.card G = 443520) (hP : Nat.card P = 11)
    (hC : Nat.card (Subgroup.centralizer (P : Set G)) ∣ 242) :
    Nat.card (Subgroup.normalizer (P : Set G)) = 55 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : IsCyclic P := isCyclic_of_prime_card hP
  have hAut : Nat.card (MulAut P) = 10 := by
    rw [IsCyclic.card_mulAut,hP]
    decide +kernel
  let N := Subgroup.normalizer (P : Set G)
  have hd : Nat.card N ∣ 2420 := by
    have h := (normalizer_card_dvd_centralizer_mul_aut (P : Subgroup G)).trans
      (Nat.mul_dvd_mul hC (dvd_refl (Nat.card (MulAut P))))
    simpa only [hAut] using h
  have hdG : Nat.card N ∣ 443520 := by
    rw [←hG]
    exact N.card_subgroup_dvd_card
  have hd220 : Nat.card N ∣ 220 := by
    simpa only [show Nat.gcd 2420 443520 = 220 by decide +kernel] using Nat.dvd_gcd hd hdG
  have hp := N.card_mul_index
  rw [hG] at hp
  have hi : N.index = 443520 / Nat.card N := by
    rw [←hp,Nat.mul_div_cancel_left _ (Nat.card_pos (α := N))]
  have hm := card_sylow_modEq_one 11 G
  rw [P.card_eq_index_normalizer] at hm
  change N.index % 11 = 1 % 11 at hm
  rw [hi] at hm
  exact divisor_receipt _ (Nat.mem_divisors.mpr ⟨hd220,by decide⟩) (by simpa using hm)

theorem centralizer_card_eq_eleven (P : Sylow 11 G)
    (hG : Nat.card G = 443520) (hP : Nat.card P = 11)
    (hC : Nat.card (Subgroup.centralizer (P : Set G)) ∣ 242) :
    Nat.card (Subgroup.centralizer (P : Set G)) = 11 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : IsCyclic P := isCyclic_of_prime_card hP
  letI : CommGroup P := IsCyclic.commGroup
  let C := Subgroup.centralizer (P : Set G)
  have hdN := Subgroup.card_dvd_of_le (Subgroup.centralizer_le_normalizer (P : Set G))
  rw [normalizer_card_eq_fiftyFive P hG hP hC] at hdN
  have hd : Nat.card C ∣ 11 := by
    simpa only [show Nat.gcd 242 55 = 11 by decide] using Nat.dvd_gcd hC hdN
  let f : P → C := fun x => ⟨x.val,by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : P) x)⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : C => (z : G)) he)
  exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hd)
    (calc
      11 = Nat.card P := hP.symm
      _ ≤ Nat.card C := Nat.card_le_card_of_injective f hf)

end SymmetricSubgroupAsymptotics.CyclicSylowElevenNormalizerCard
