import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualRepresentation
import SymmetricSubgroupAsymptotics.SimpleTwoGeneratorConjugateNormalClosure
import SymmetricSubgroupAsymptotics.TwelvePointTernarySylowNormalizerSolvable
import Mathlib.Tactic.FinCases

/-! The inherited simple pinned M12 presentation has good Sylow prime3.
The injective literal representation supplies the faithful12-action, order
divisibility, and four3-cycle element. The involutory presentation generator
conjugates that3-element to a second generating3-subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveGoodSylowThree
open CFSG.Models.Presentations.M12
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def pinnedX : Model := PresentedGroup.of (0 : Fin 2)
def pinnedY : Model := PresentedGroup.of (1 : Fin 2)

theorem pinnedX_square : pinnedX ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ relators}) (x := (FreeGroup.of (0 : Fin 2)) ^ 2)
    (by change _ ∈ relators; exact List.mem_cons_self)
  simpa only [pinnedX, map_pow, PresentedGroup.of] using h

theorem pinnedY_cube : pinnedY ^ 3 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ relators}) (x := (FreeGroup.of (1 : Fin 2)) ^ 3)
    (by change _ ∈ relators; exact List.mem_cons_of_mem _ List.mem_cons_self)
  simpa only [pinnedY, map_pow, PresentedGroup.of] using h

theorem pinnedY_ne_one : pinnedY ≠ 1 := by
  intro h
  have he := congrArg CFSGMathieuTwelveActualRepresentation.representation h
  rw [map_one] at he
  change CFSGMathieuTwelveActualRepresentation.representation
    (PresentedGroup.of (1 : Fin 2)) = 1 at he
  rw [CFSGMathieuTwelveActualRepresentation.representation_of_one] at he
  exact CFSGMathieuTwelvePresentationWords.y_ne_one he

theorem pinnedY_order : orderOf pinnedY = 3 :=
  orderOf_eq_prime pinnedY_cube pinnedY_ne_one

theorem pinnedY_cycleType :
    (CFSGMathieuTwelveActualRepresentation.permutationRepresentation pinnedY).cycleType =
      Multiset.replicate 4 3 := by
  change (CFSGMathieuTwelveActualRepresentation.permutationRepresentation
    (PresentedGroup.of (1 : Fin 2))).cycleType = _
  rw [CFSGMathieuTwelveActualRepresentation.permutationRepresentation_of_one]
  exact CFSGMathieuTwelvePresentationWords.yPermutation_cycleType

theorem presentation_pair_closure : Subgroup.closure ({pinnedX, pinnedY} : Set Model) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of {w | w ∈ relators}]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure (by simp [pinnedX])
  · exact Subgroup.subset_closure (by simp [pinnedY])

theorem conjugate_zpowers_isPGroup :
    IsPGroup 3 (Subgroup.zpowers (pinnedX * pinnedY * pinnedX⁻¹)) := by
  have hc : (pinnedX * pinnedY * pinnedX⁻¹) ^ 3 = 1 := by
    have h := congrArg (MulAut.conj pinnedX) pinnedY_cube
    simpa only [map_pow, map_one, MulAut.conj_apply] using h
  have hd : Nat.card (Subgroup.zpowers (pinnedX * pinnedY * pinnedX⁻¹)) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hc
  rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ hd with h | h
  · exact IsPGroup.of_card (n := 0) (by simpa only [pow_zero] using h)
  · exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using h)

theorem conjugate_zpowers_sup_eq_top [IsSimpleGroup Model] :
    Subgroup.zpowers (pinnedX * pinnedY * pinnedX⁻¹) ⊔ Subgroup.zpowers pinnedY = ⊤ := by
  rw [sup_comm]
  exact SimpleTwoGeneratorConjugateNormalClosure.zpowers_sup_eq_top
    pinnedX pinnedY pinnedX_square pinnedY_ne_one presentation_pair_closure

theorem goodSylowPrime [Finite Model] [IsSimpleGroup Model] :
    CFSGReduction.GoodSylowPrime Model 3 := by
  letI : MulAction Model (Fin 12) := MulAction.compHom (Fin 12)
    CFSGMathieuTwelveActualRepresentation.permutationRepresentation
  letI : FaithfulSMul Model (Fin 12) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      CFSGMathieuTwelveActualRepresentation.permutationRepresentation_injective
        (Equiv.Perm.ext hab) }
  apply TwelvePointTernarySylowNormalizerSolvable.goodSylowPrime_of_two_p_subgroups
    (Subgroup.zpowers (pinnedX * pinnedY * pinnedX⁻¹)) conjugate_zpowers_isPGroup
    CFSGMathieuTwelveActualRepresentation.card_dvd pinnedY pinnedY_order
  · have he : MulAction.toPermHom Model (Fin 12) pinnedY =
        CFSGMathieuTwelveActualRepresentation.permutationRepresentation pinnedY := by
      ext i
      rfl
    rw [he]
    exact pinnedY_cycleType
  · exact conjugate_zpowers_sup_eq_top

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveGoodSylowThree
