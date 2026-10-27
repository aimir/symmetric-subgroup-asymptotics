import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu12.Cardinality
import Mathlib.SetTheory.Cardinal.Finite

/-! A factorized complete cover of the SAME original12-point M12 by its
five checked stabilizer-chain transversals, with base0,1,2,3,4. The50 seed
slots give12*11*10*9*8 codes. Successive base-point images prove injection;
the checked actual order95040 then gives bijection. No group elements,
action table, or accepted-image capacity are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTransversalCover
open CFSG.Certificates.Mathieu12 M12Certificates M12Certificates.StabilizerChain

abbrev Second : Type := {j : Fin 12 // j ≠ 0}
abbrev Third : Type := {k : Fin 12 // k ≠ 0 ∧ k ≠ 1}
abbrev Fourth : Type := {l : Fin 12 // l ≠ 0 ∧ l ≠ 1 ∧ l ≠ 2}
abbrev Fifth : Type := {m : Fin 12 // m ≠ 0 ∧ m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 3}
abbrev Code : Type := (Fin 12 × Second) × (Third × (Fourth × Fifth))

def first (i : Fin 12) : M12 := Word.toM12 (orbitZeroWord i)
def second (j : Second) : M12 := (zeroStabilizerElement j.val j.property).val
def third (k : Third) : M12 :=
  (zeroOneStabilizerElement k.val k.property.1 k.property.2).val.val
def fourth (l : Fourth) : M12 :=
  (zeroOneTwoStabilizerElement l.val l.property.1 l.property.2.1 l.property.2.2).val.val.val
def fifth (m : Fifth) : M12 :=
  (zeroOneTwoThreeStabilizerElement m.val m.property.1 m.property.2.1
    m.property.2.2.1 m.property.2.2.2).val.val.val.val

theorem first_zero (i : Fin 12) : (first i).val 0 = i := orbitZeroWord_maps_zero_all i
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
  zeroOneTwoStabilizerWord_fixes_zero_all l.val l.property.1 l.property.2.1 l.property.2.2
theorem fourth_one (l : Fourth) : (fourth l).val 1 = 1 :=
  zeroOneTwoStabilizerWord_fixes_one_all l.val l.property.1 l.property.2.1 l.property.2.2
theorem fourth_two (l : Fourth) : (fourth l).val 2 = 2 :=
  zeroOneTwoStabilizerWord_fixes_two_all l.val l.property.1 l.property.2.1 l.property.2.2
theorem fourth_three (l : Fourth) : (fourth l).val 3 = l.val :=
  zeroOneTwoStabilizerWord_maps_three_all l.val l.property.1 l.property.2.1 l.property.2.2
theorem fifth_zero (m : Fifth) : (fifth m).val 0 = 0 :=
  zeroOneTwoThreeStabilizerWord_fixes_zero_all m.val m.property.1 m.property.2.1
    m.property.2.2.1 m.property.2.2.2
theorem fifth_one (m : Fifth) : (fifth m).val 1 = 1 :=
  zeroOneTwoThreeStabilizerWord_fixes_one_all m.val m.property.1 m.property.2.1
    m.property.2.2.1 m.property.2.2.2
theorem fifth_two (m : Fifth) : (fifth m).val 2 = 2 :=
  zeroOneTwoThreeStabilizerWord_fixes_two_all m.val m.property.1 m.property.2.1
    m.property.2.2.1 m.property.2.2.2
theorem fifth_three (m : Fifth) : (fifth m).val 3 = 3 :=
  zeroOneTwoThreeStabilizerWord_fixes_three_all m.val m.property.1 m.property.2.1
    m.property.2.2.1 m.property.2.2.2
theorem fifth_four (m : Fifth) : (fifth m).val 4 = m.val :=
  zeroOneTwoThreeStabilizerWord_maps_four_all m.val m.property.1 m.property.2.1
    m.property.2.2.1 m.property.2.2.2

def decode (c : Code) : M12 :=
  first c.1.1 * second c.1.2 * third c.2.1 * fourth c.2.2.1 * fifth c.2.2.2

theorem decode_injective : Function.Injective decode := by
  rintro ⟨⟨i,j⟩,⟨k,⟨l,m⟩⟩⟩ ⟨⟨i',j'⟩,⟨k',⟨l',m'⟩⟩⟩ he
  have hi : i = i' := by
    have h := congrArg (fun g : M12 => g.val (0 : Fin 12)) he
    simpa only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fifth_zero,fourth_zero,third_zero,second_zero,first_zero] using h
  subst i'
  have h1 : second j * third k * fourth l * fifth m =
      second j' * third k' * fourth l' * fifth m' := by
    apply mul_left_cancel (a := first i)
    simpa only [decode,mul_assoc] using he
  have hj : j = j' := by
    apply Subtype.ext
    have h := congrArg (fun g : M12 => g.val (1 : Fin 12)) h1
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fifth_one,fourth_one,third_one,second_one] using h
  subst j'
  have h2 : third k * fourth l * fifth m = third k' * fourth l' * fifth m' := by
    apply mul_left_cancel (a := second j)
    simpa only [mul_assoc] using h1
  have hk : k = k' := by
    apply Subtype.ext
    have h := congrArg (fun g : M12 => g.val (2 : Fin 12)) h2
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fifth_two,fourth_two,third_two] using h
  subst k'
  have h3 : fourth l * fifth m = fourth l' * fifth m' := by
    apply mul_left_cancel (a := third k)
    simpa only [mul_assoc] using h2
  have hl : l = l' := by
    apply Subtype.ext
    have h := congrArg (fun g : M12 => g.val (3 : Fin 12)) h3
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fifth_three,fourth_three] using h
  subst l'
  have h4 : fifth m = fifth m' := mul_left_cancel h3
  have hm : m = m' := by
    apply Subtype.ext
    have h := congrArg (fun g : M12 => g.val (4 : Fin 12)) h4
    simpa only [fifth_four] using h
  subst m'
  rfl

theorem code_card : Nat.card Code = 95040 := by
  have h2 : Nat.card Second = 11 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h3 : Nat.card Third = 10 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h4 : Nat.card Fourth = 9 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h5 : Nat.card Fifth = 8 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  simp only [Code,Nat.card_prod,Nat.card_fin,h2,h3,h4,h5]

theorem decode_bijective : Function.Bijective decode :=
  (Nat.bijective_iff_injective_and_card decode).mpr
    ⟨decode_injective,code_card.trans M12Cardinality.card_M12.symm⟩

theorem decode_surjective : Function.Surjective decode := decode_bijective.2

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTransversalCover
