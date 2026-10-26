import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualRepresentation
import SymmetricSubgroupAsymptotics.ElevenPointBinarySylowNormalizerSolvable
import Mathlib.Tactic.FinCases

/-! The inherited simple pinned M11 presentation has good Sylow prime2.
Its own two presentation generators are2-elements and generate it; the
literal injective11-point representation pays the actual normalizer
through the generic double-four-cycle theorem. No surjectivity or target
model identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenGoodSylowTwo
open CFSG.Models.Presentations.M11

def pinnedX : Model := PresentedGroup.of (0 : Fin 2)
def pinnedY : Model := PresentedGroup.of (1 : Fin 2)

def permutationRepresentation : Model →* Equiv.Perm (Fin 11) :=
  CFSG.Certificates.Mathieu11.M11Subgroup.subtype.comp
    CFSGMathieuElevenActualRepresentation.representation

theorem permutationRepresentation_injective [IsSimpleGroup Model] :
    Function.Injective permutationRepresentation :=
  CFSG.Certificates.Mathieu11.M11Subgroup.subtype_injective.comp
    CFSGMathieuElevenActualRepresentation.representation_injective

theorem permutationRepresentation_pinnedY :
    permutationRepresentation pinnedY=CFSG.Certificates.Mathieu11.m11b := by
  change (CFSGMathieuElevenActualRepresentation.representation
    (PresentedGroup.of (1 : Fin 2))).val=CFSG.Certificates.Mathieu11.m11b
  rw [CFSGMathieuElevenActualRepresentation.representation_of_one]
  rfl

theorem pinnedX_square : pinnedX^2=1 := by
  have h := PresentedGroup.one_of_mem
    (rels:={w|w∈relators}) (x:=(FreeGroup.of (0 : Fin 2))^2)
    (by change _∈relators; exact List.mem_cons_self)
  simpa only [pinnedX,map_pow,PresentedGroup.of] using h

theorem pinnedY_fourth : pinnedY^4=1 := by
  have h := PresentedGroup.one_of_mem
    (rels:={w|w∈relators}) (x:=(FreeGroup.of (1 : Fin 2))^4)
    (by change _∈relators
        exact List.mem_cons_of_mem _ List.mem_cons_self)
  simpa only [pinnedY,map_pow,PresentedGroup.of] using h

theorem pinnedY_order : orderOf pinnedY=4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : pinnedY^2≠1 := by
    have hmove : (CFSG.Certificates.Mathieu11.m11b^2) (2 : Fin 11)≠2 := by decide +kernel
    intro h
    have he := congrArg permutationRepresentation h
    rw [map_pow,permutationRepresentation_pinnedY,map_one] at he
    exact hmove (congrArg (fun σ : Equiv.Perm (Fin 11) => σ (2 : Fin 11)) he)
  exact orderOf_eq_prime_pow (p:=2) (n:=1) hsq pinnedY_fourth

theorem pinnedY_cycleType :
    (permutationRepresentation pinnedY).cycleType=Multiset.replicate 2 4 := by
  rw [permutationRepresentation_pinnedY]
  decide +kernel

theorem zpowers_sup_eq_top : Subgroup.zpowers pinnedX⊔Subgroup.zpowers pinnedY=⊤ := by
  apply top_unique
  rw [←PresentedGroup.closure_range_of {w|w∈relators}]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers pinnedX)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers pinnedY)

theorem pinnedX_zpowers_isPGroup : IsPGroup 2 (Subgroup.zpowers pinnedX) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : Nat.card (Subgroup.zpowers pinnedX)∣2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one pinnedX_square
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h|h
  · exact IsPGroup.of_card (n:=0) (by simpa only [pow_zero] using h)
  · exact IsPGroup.of_card (n:=1) (by simpa only [pow_one] using h)

theorem goodSylowPrime [Finite Model] [IsSimpleGroup Model] :
    CFSGReduction.GoodSylowPrime Model 2 := by
  letI : MulAction Model (Fin 11) := MulAction.compHom (Fin 11) permutationRepresentation
  letI : FaithfulSMul Model (Fin 11) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      permutationRepresentation_injective (Equiv.Perm.ext hab) }
  apply ElevenPointBinarySylowNormalizerSolvable.goodSylowPrime_of_two_p_subgroups
    (Subgroup.zpowers pinnedX) pinnedX_zpowers_isPGroup
    CFSGMathieuElevenActualRepresentation.card_dvd pinnedY pinnedY_order
  · have he : MulAction.toPermHom Model (Fin 11) pinnedY=permutationRepresentation pinnedY := by
      ext i
      rfl
    rw [he]
    exact pinnedY_cycleType
  · exact zpowers_sup_eq_top

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenGoodSylowTwo
