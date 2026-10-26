import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu11.Cardinality
import Mathlib.SetTheory.Cardinal.Finite

/-! A factorized complete cover of the SAME original M11 by its four
already checked stabilizer-chain transversals. There are only38 seed
words; no group elements or action table are enumerated. Injectivity is
proved from their successive base-point images, and actual order7920
then supplies surjectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalCover
open CFSG.Certificates.Mathieu11 M11Certificates M11Certificates.StabilizerChain

abbrev Second : Type := {j : Fin 11 // j≠0}
abbrev Third : Type := {k : Fin 11 // k≠0 ∧ k≠1}
abbrev Fourth : Type := {l : Fin 11 // l≠0 ∧ l≠1 ∧ l≠2}
abbrev Code : Type := (Fin 11 × Second) × (Third × Fourth)

def first (i : Fin 11) : M11 := Word.toM11 (aPowerWord i.val)
def second (j : Second) : M11 := (zeroStabilizerElement j.val j.property).val
def third (k : Third) : M11 :=
  (zeroOneStabilizerElement k.val k.property.1 k.property.2).val.val
def fourth (l : Fourth) : M11 :=
  (zeroOneTwoStabilizerElement l.val l.property.1 l.property.2.1 l.property.2.2).val.val.val

theorem first_zero (i : Fin 11) : (first i).val 0=i := aPowerWord_maps_zero i
theorem second_zero (j : Second) : (second j).val 0=0 :=
  zeroStabilizerWord_fixes_zero j.val j.property
theorem second_one (j : Second) : (second j).val 1=j.val :=
  zeroStabilizerWord_maps_one j.val j.property
theorem third_zero (k : Third) : (third k).val 0=0 :=
  zeroOneStabilizerWord_fixes_zero k.val k.property.1 k.property.2
theorem third_one (k : Third) : (third k).val 1=1 :=
  zeroOneStabilizerWord_fixes_one k.val k.property.1 k.property.2
theorem third_two (k : Third) : (third k).val 2=k.val :=
  zeroOneStabilizerWord_maps_two k.val k.property.1 k.property.2
theorem fourth_zero (l : Fourth) : (fourth l).val 0=0 :=
  zeroOneTwoStabilizerWord_fixes_zero l.val l.property.1 l.property.2.1 l.property.2.2
theorem fourth_one (l : Fourth) : (fourth l).val 1=1 :=
  zeroOneTwoStabilizerWord_fixes_one l.val l.property.1 l.property.2.1 l.property.2.2
theorem fourth_two (l : Fourth) : (fourth l).val 2=2 :=
  zeroOneTwoStabilizerWord_fixes_two l.val l.property.1 l.property.2.1 l.property.2.2
theorem fourth_three (l : Fourth) : (fourth l).val 3=l.val :=
  zeroOneTwoStabilizerWord_maps_three l.val l.property.1 l.property.2.1 l.property.2.2

def decode (c : Code) : M11 := first c.1.1*second c.1.2*third c.2.1*fourth c.2.2

theorem decode_injective : Function.Injective decode := by
  rintro ⟨⟨i,j⟩,⟨k,l⟩⟩ ⟨⟨i',j'⟩,⟨k',l'⟩⟩ he
  have hi : i=i' := by
    have h := congrArg (fun g : M11 => g.val (0 : Fin 11)) he
    simpa only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fourth_zero,third_zero,second_zero,first_zero] using h
  subst i'
  have h1 : second j*third k*fourth l=second j'*third k'*fourth l' := by
    apply mul_left_cancel (a:=first i)
    simpa only [decode,mul_assoc] using he
  have hj : j=j' := by
    apply Subtype.ext
    have h := congrArg (fun g : M11 => g.val (1 : Fin 11)) h1
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fourth_one,third_one,second_one] using h
  subst j'
  have h2 : third k*fourth l=third k'*fourth l' := by
    apply mul_left_cancel (a:=second j)
    simpa only [mul_assoc] using h1
  have hk : k=k' := by
    apply Subtype.ext
    have h := congrArg (fun g : M11 => g.val (2 : Fin 11)) h2
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fourth_two,third_two] using h
  subst k'
  have h3 : fourth l=fourth l' := mul_left_cancel h2
  have hl : l=l' := by
    apply Subtype.ext
    have h := congrArg (fun g : M11 => g.val (3 : Fin 11)) h3
    simpa only [fourth_three] using h
  subst l'
  rfl

theorem code_card : Nat.card Code=7920 := by
  have h2 : Nat.card Second=10 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h3 : Nat.card Third=9 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h4 : Nat.card Fourth=8 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  simp only [Code,Nat.card_prod,Nat.card_fin,h2,h3,h4]

theorem decode_bijective : Function.Bijective decode :=
  (Nat.bijective_iff_injective_and_card decode).mpr
    ⟨decode_injective,code_card.trans M11Cardinality.card_M11.symm⟩

theorem decode_surjective : Function.Surjective decode := decode_bijective.2

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalCover
