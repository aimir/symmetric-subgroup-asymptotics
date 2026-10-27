import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Cardinality
import Mathlib.SetTheory.Cardinal.Finite

/-! The five original M23 tail transversals give a complete443520-code
chart of the actual stabilizer of22. Only the82 existing levelTwo through
levelSix seed words are used. The tail orbit-card identities and checked
final rigidity prove completeness, without recovery of the pinned model
or enumeration of the original ten-million-element group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeStabilizerTransversalCover
open CFSG.Certificates.Mathieu23 M23Certificates
open M23Certificates.StabilizerChain M23Certificates.SteinerSystem

abbrev Stabilizer : Type := MulAction.stabilizer M23 (22 : Fin 23)
abbrev First : Type := {i : Fin 23 // i ≠ 22}
abbrev Second : Type := {j : Fin 23 // j ≠ 22 ∧ j ≠ 0}
abbrev Third : Type := {k : Fin 23 // k ≠ 22 ∧ k ≠ 0 ∧ k ≠ 1}
abbrev Fourth : Type := {l : Fin 23 // l ∈ blockB0ᶜ}
abbrev Fifth : Type := {m : Fin 23 // m = 3 ∨ m = 4 ∨ m = 21}
abbrev Code : Type := (First × Second) × (Third × (Fourth × Fifth))

def first (i : First) : M23 := Word.toM23 (levelTwoWord i.val)
def second (j : Second) : M23 := Word.toM23 (levelThreeWord j.val)
def third (k : Third) : M23 := Word.toM23 (levelFourWord k.val)
def fourth (l : Fourth) : M23 := Word.toM23 (levelFiveWord l.val)
def fifth (m : Fifth) : M23 := Word.toM23 (levelSixWord m.val)

theorem first_last (i : First) : (first i).val 22 = 22 :=
  levelTwoWord_fixes_last_all i.val i.property
theorem first_zero (i : First) : (first i).val 0 = i.val :=
  levelTwoWord_maps_zero_all i.val i.property
theorem second_last (j : Second) : (second j).val 22 = 22 :=
  levelThreeWord_fixes_last_all j.val j.property.1 j.property.2
theorem second_zero (j : Second) : (second j).val 0 = 0 :=
  levelThreeWord_fixes_zero_all j.val j.property.1 j.property.2
theorem second_one (j : Second) : (second j).val 1 = j.val :=
  levelThreeWord_maps_one_all j.val j.property.1 j.property.2
theorem third_last (k : Third) : (third k).val 22 = 22 :=
  levelFourWord_fixes_last_all k.val k.property.1 k.property.2.1 k.property.2.2
theorem third_zero (k : Third) : (third k).val 0 = 0 :=
  levelFourWord_fixes_zero_all k.val k.property.1 k.property.2.1 k.property.2.2
theorem third_one (k : Third) : (third k).val 1 = 1 :=
  levelFourWord_fixes_one_all k.val k.property.1 k.property.2.1 k.property.2.2
theorem third_two (k : Third) : (third k).val 2 = k.val :=
  levelFourWord_maps_two_all k.val k.property.1 k.property.2.1 k.property.2.2
theorem fourth_last (l : Fourth) : (fourth l).val 22 = 22 :=
  levelFiveWord_fixes_last_all l.val l.property
theorem fourth_zero (l : Fourth) : (fourth l).val 0 = 0 :=
  levelFiveWord_fixes_zero_all l.val l.property
theorem fourth_one (l : Fourth) : (fourth l).val 1 = 1 :=
  levelFiveWord_fixes_one_all l.val l.property
theorem fourth_two (l : Fourth) : (fourth l).val 2 = 2 :=
  levelFiveWord_fixes_two_all l.val l.property
theorem fourth_five (l : Fourth) : (fourth l).val 5 = l.val :=
  levelFiveWord_maps_five_all l.val l.property
theorem fifth_last (m : Fifth) : (fifth m).val 22 = 22 :=
  levelSixWord_fixes_last_all m.val m.property
theorem fifth_zero (m : Fifth) : (fifth m).val 0 = 0 :=
  levelSixWord_fixes_zero_all m.val m.property
theorem fifth_one (m : Fifth) : (fifth m).val 1 = 1 :=
  levelSixWord_fixes_one_all m.val m.property
theorem fifth_two (m : Fifth) : (fifth m).val 2 = 2 :=
  levelSixWord_fixes_two_all m.val m.property
theorem fifth_five (m : Fifth) : (fifth m).val 5 = 5 :=
  levelSixWord_fixes_five_all m.val m.property
theorem fifth_three (m : Fifth) : (fifth m).val 3 = m.val :=
  levelSixWord_maps_three_all m.val m.property

def wordDecode (c : Code) : M23 :=
  first c.1.1 * second c.1.2 * third c.2.1 * fourth c.2.2.1 * fifth c.2.2.2

theorem wordDecode_last (c : Code) : (wordDecode c).val 22 = 22 := by
  simp only [wordDecode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
    fifth_last,fourth_last,third_last,second_last,first_last]

def decode (c : Code) : Stabilizer := ⟨wordDecode c,by
  rw [MulAction.mem_stabilizer_iff]
  change (wordDecode c).val 22 = 22
  exact wordDecode_last c⟩

theorem wordDecode_injective : Function.Injective wordDecode := by
  rintro ⟨⟨i,j⟩,⟨k,⟨l,m⟩⟩⟩ ⟨⟨i',j'⟩,⟨k',⟨l',m'⟩⟩⟩ he
  have hi : i = i' := by
    apply Subtype.ext
    have h := congrArg (fun g : M23 => g.val (0 : Fin 23)) he
    simpa only [wordDecode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fifth_zero,fourth_zero,third_zero,second_zero,first_zero] using h
  subst i'
  have h1 : second j * third k * fourth l * fifth m =
      second j' * third k' * fourth l' * fifth m' := by
    apply mul_left_cancel (a := first i)
    simpa only [wordDecode,mul_assoc] using he
  have hj : j = j' := by
    apply Subtype.ext
    have h := congrArg (fun g : M23 => g.val (1 : Fin 23)) h1
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,
      fifth_one,fourth_one,third_one,second_one] using h
  subst j'
  have h2 : third k * fourth l * fifth m = third k' * fourth l' * fifth m' := by
    apply mul_left_cancel (a := second j)
    simpa only [mul_assoc] using h1
  have hk : k = k' := by
    apply Subtype.ext
    have h := congrArg (fun g : M23 => g.val (2 : Fin 23)) h2
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fifth_two,fourth_two,third_two] using h
  subst k'
  have h3 : fourth l * fifth m = fourth l' * fifth m' := by
    apply mul_left_cancel (a := third k)
    simpa only [mul_assoc] using h2
  have hl : l = l' := by
    apply Subtype.ext
    have h := congrArg (fun g : M23 => g.val (5 : Fin 23)) h3
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,fifth_five,fourth_five] using h
  subst l'
  have h4 : fifth m = fifth m' := mul_left_cancel h3
  have hm : m = m' := by
    apply Subtype.ext
    have h := congrArg (fun g : M23 => g.val (3 : Fin 23)) h4
    simpa only [fifth_three] using h
  subst m'
  rfl

theorem decode_injective : Function.Injective decode := by
  intro c d he
  exact wordDecode_injective (congrArg Subtype.val he)

theorem code_card : Nat.card Code = 443520 := by
  have h1 : Nat.card First = 22 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h2 : Nat.card Second = 21 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h3 : Nat.card Third = 20 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h4 : Nat.card Fourth = 16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h5 : Nat.card Fifth = 3 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  simp only [Code,Nat.card_prod,h1,h2,h3,h4,h5]

theorem stabilizer_card : Nat.card Stabilizer = 443520 := by
  change Nat.card M23Cardinality.Stab22 = 443520
  rw [M23Cardinality.card_stab22_eq_second_orbit_mul_stabilizer,
    M23Cardinality.card_stab220_eq_third_orbit_mul_stabilizer,
    M23Cardinality.card_stab2201_eq_fourth_orbit_mul_stabilizer,
    M23Cardinality.card_stab22012_eq_fifth_orbit_mul_stabilizer,
    M23Cardinality.card_stab220125_eq_sixth_orbit_mul_stabilizer,
    M23Cardinality.final_stabilizer_card_one]

theorem decode_bijective : Function.Bijective decode :=
  (Nat.bijective_iff_injective_and_card decode).mpr
    ⟨decode_injective,code_card.trans stabilizer_card.symm⟩

theorem decode_surjective : Function.Surjective decode := decode_bijective.2

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeStabilizerTransversalCover
