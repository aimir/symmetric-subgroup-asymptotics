import SymmetricSubgroupAsymptotics.CFSGOddRotationAbelianPairs
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J3
import Mathlib.Tactic.FinCases

/-! The literal old J3 relators imply abelian conjugate-pair generation.
This is a statement about that exact presented group, without recognition,
simplicity, a named order, or an extra Bray-element power. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGJankoThreeAbelianPair

open CFSG.Models CFSG.Models.Presentations.J3

def pinnedX : Model := PresentedGroup.of (0 : Fin 2)
def pinnedY : Model := PresentedGroup.of (1 : Fin 2)

theorem pinnedX_square : pinnedX ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ relators}) (x := (FreeGroup.of (0 : Fin 2)) ^ 2)
    (by change _ ∈ relators; exact List.mem_cons_self)
  simpa only [pinnedX, map_pow, PresentedGroup.of] using h

theorem pinned_comm_ninth : (commWord pinnedX pinnedY) ^ 9 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ relators})
    (x := (commWord (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2))) ^ 9)
    (by
      change _ ∈ relators
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simpa only [commWord, pinnedX, pinnedY, map_pow, map_mul, map_inv,
    PresentedGroup.of] using h

theorem presentation_pair_closure :
    Subgroup.closure ({pinnedX, pinnedY} : Set Model) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of {w | w ∈ relators}]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure (by simp [pinnedX])
  · exact Subgroup.subset_closure (by simp [pinnedY])

theorem rotation_ninth : (pinnedX * (pinnedY⁻¹ * pinnedX * pinnedY)) ^ 9 = 1 := by
  have hi : pinnedX⁻¹ = pinnedX :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using pinnedX_square)
  simpa only [commWord, hi, mul_assoc] using pinned_comm_ninth

theorem soluble_pair :
    ∃ (U : Subgroup Model) (g : Model), IsSolvable U ∧
      Subgroup.closure ((U : Set Model) ∪ U.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  exact CFSGOddRotationAbelianPairs.soluble_pair pinnedX pinnedY 4
    pinnedX_square rotation_ninth presentation_pair_closure

end SymmetricSubgroupAsymptotics.CFSGJankoThreeAbelianPair
