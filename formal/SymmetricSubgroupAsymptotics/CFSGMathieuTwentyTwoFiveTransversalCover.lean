import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu22.Cardinality
import Mathlib.SetTheory.Cardinal.Finite

/-! A factorized complete cover of the SAME original22-point M22 by
its five already checked stabilizer-chain transversals. The base is
0,1,2,5,3 and there are82 seed slots. Successive base-point images prove
injectivity; the checked actual order443520 then proves surjectivity.
No group elements, action table, or accepted-image capacity is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoFiveTransversalCover
open CFSG.Certificates.Mathieu22 M22Certificates
open M22Certificates.StabilizerChain M22Certificates.ChainOrbits M22Certificates.SteinerSystem

abbrev Second : Type := {j : Fin 22 // j ≠ 0}
abbrev Third : Type := {k : Fin 22 // k ≠ 0 ∧ k ≠ 1}
abbrev Fourth : Type := {l : Fin 22 // l ∈ blockB0ᶜ}
abbrev Fifth : Type := {m : Fin 22 // m = 3 ∨ m = 4 ∨ m = 21}
abbrev Code : Type := (Fin 22 × Second) × (Third × (Fourth × Fifth))

def first (i : Fin 22) : M22 := Word.toM22 (orbitZeroWord i)
def second (j : Second) : M22 := (zeroStabilizerElement j.val j.property).val
def third (k : Third) : M22 :=
  (zeroOneStabilizerElement k.val k.property.1 k.property.2).val.val
def fourth (l : Fourth) : M22 := (levelFourElement l.val l.property).val.val.val
def fifth (m : Fifth) : M22 := (levelFiveElement m.val m.property).val.val.val.val

theorem first_zero (i : Fin 22) : (first i).val 0 = i := orbitZeroWord_maps_zero_all i
theorem second_zero (j : Second) : (second j).val 0 = 0 :=
  zeroStabilizerWord_fixes_zero_all j.val j.property
theorem second_one (j : Second) : (second j).val 1 = j.val :=
  zeroStabilizerWord_maps_one_all j.val j.property
theorem third_zero (k : Third) : (third k).val 0 = 0 :=
  zeroOneStabilizerWord_fixes_zero_all k.val k.property.1 k.property.2
theorem third_one (k : Third) : (third k).val 1 = 1 :=
  zeroOneStabilizerWord_fixes_one_all k.val k.property.1 k.property.2
theorem third_two (k : Third) : (third k).val 2 = k.val :=
  zeroOneStabilizerWord_maps_two_all k.val k.property.1 k.property.2
theorem fourth_zero (l : Fourth) : (fourth l).val 0 = 0 :=
  levelFourWord_fixes_zero_all l.val l.property
theorem fourth_one (l : Fourth) : (fourth l).val 1 = 1 :=
  levelFourWord_fixes_one_all l.val l.property
theorem fourth_two (l : Fourth) : (fourth l).val 2 = 2 :=
  levelFourWord_fixes_two_all l.val l.property
theorem fourth_five (l : Fourth) : (fourth l).val 5 = l.val :=
  levelFourWord_maps_five_all l.val l.property
theorem fifth_zero (m : Fifth) : (fifth m).val 0 = 0 :=
  levelFiveWord_fixes_zero_all m.val m.property
theorem fifth_one (m : Fifth) : (fifth m).val 1 = 1 :=
  levelFiveWord_fixes_one_all m.val m.property
theorem fifth_two (m : Fifth) : (fifth m).val 2 = 2 :=
  levelFiveWord_fixes_two_all m.val m.property
theorem fifth_five (m : Fifth) : (fifth m).val 5 = 5 :=
  levelFiveWord_fixes_five_all m.val m.property
theorem fifth_three (m : Fifth) : (fifth m).val 3 = m.val :=
  levelFiveWord_maps_three_all m.val m.property

def decode (c : Code) : M22 :=
  first c.1.1 * second c.1.2 * third c.2.1 * fourth c.2.2.1 * fifth c.2.2.2

theorem decode_injective : Function.Injective decode := by
  rintro ⟨⟨i,j⟩,⟨k,⟨l,m⟩⟩⟩ ⟨⟨i',j'⟩,⟨k',⟨l',m'⟩⟩⟩ he
  have hi : i = i' := by
    have h := congrArg (fun g : M22 => g.val (0 : Fin 22)) he
    simpa only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fifth_zero,fourth_zero,third_zero,second_zero,first_zero] using h
  subst i'
  have h1 : second j * third k * fourth l * fifth m =
      second j' * third k' * fourth l' * fifth m' := by
    apply mul_left_cancel (a := first i)
    simpa only [decode,mul_assoc] using he
  have hj : j = j' := by
    apply Subtype.ext
    have h := congrArg (fun g : M22 => g.val (1 : Fin 22)) h1
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fifth_one,fourth_one,third_one,second_one] using h
  subst j'
  have h2 : third k * fourth l * fifth m = third k' * fourth l' * fifth m' := by
    apply mul_left_cancel (a := second j)
    simpa only [mul_assoc] using h1
  have hk : k = k' := by
    apply Subtype.ext
    have h := congrArg (fun g : M22 => g.val (2 : Fin 22)) h2
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fifth_two,fourth_two,third_two] using h
  subst k'
  have h3 : fourth l * fifth m = fourth l' * fifth m' := by
    apply mul_left_cancel (a := third k)
    simpa only [mul_assoc] using h2
  have hl : l = l' := by
    apply Subtype.ext
    have h := congrArg (fun g : M22 => g.val (5 : Fin 22)) h3
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fifth_five,fourth_five] using h
  subst l'
  have h4 : fifth m = fifth m' := mul_left_cancel h3
  have hm : m = m' := by
    apply Subtype.ext
    have h := congrArg (fun g : M22 => g.val (3 : Fin 22)) h4
    simpa only [fifth_three] using h
  subst m'
  rfl

theorem code_card : Nat.card Code = 443520 := by
  have h2 : Nat.card Second = 21 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h3 : Nat.card Third = 20 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h4 : Nat.card Fourth = 16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h5 : Nat.card Fifth = 3 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  simp only [Code,Nat.card_prod,Nat.card_fin,h2,h3,h4,h5]

theorem decode_bijective : Function.Bijective decode :=
  (Nat.bijective_iff_injective_and_card decode).mpr
    ⟨decode_injective,code_card.trans M22Cardinality.card_M22.symm⟩

theorem decode_surjective : Function.Surjective decode := decode_bijective.2

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoFiveTransversalCover
