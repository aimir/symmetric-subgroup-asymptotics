import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J1
import Mathlib.Tactic.FinCases

/-! Original pinned J1 presentation generators and WHOLE relator powers.
No representation, named-group order, nontriviality or model equivalence
is assumed. Powers dividing2/3/7 are not asserted to be exact orders. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGJankoOnePresentationGenerators
open CFSG.Models.Presentations.J1

def pinnedX : Model := PresentedGroup.of (0 : Fin 2)
def pinnedY : Model := PresentedGroup.of (1 : Fin 2)
def lastInvolutionWord {G : Type} [Group G] (x y : G) : G :=
  (x*y)*((x*y*x*((y⁻¹)^1))^6)*x*y*x*y*((x*((y⁻¹)^1))^2)
def pinnedZ : Model := lastInvolutionWord pinnedX pinnedY

theorem pinnedX_square : pinnedX^2=1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w∈relators}) (x := (FreeGroup.of (0 : Fin 2))^2)
    (by change _∈relators; exact List.mem_cons_self)
  simpa only [pinnedX,map_pow,PresentedGroup.of] using h

theorem pinnedY_cube : pinnedY^3=1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w∈relators}) (x := (FreeGroup.of (1 : Fin 2))^3)
    (by change _∈relators; exact List.mem_cons_of_mem _ List.mem_cons_self)
  simpa only [pinnedY,map_pow,PresentedGroup.of] using h

theorem pinnedProduct_seventh : (pinnedX*pinnedY)^7=1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w∈relators})
    (x := ((FreeGroup.of (0 : Fin 2))*(FreeGroup.of (1 : Fin 2)))^7)
    (by change _∈relators; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simpa only [pinnedX,pinnedY,map_pow,map_mul,PresentedGroup.of] using h

theorem pinnedZ_square : pinnedZ^2=1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w∈relators})
    (x := (lastInvolutionWord (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2)))^2)
    (by
      change _∈relators
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  simpa only [pinnedZ,lastInvolutionWord,pinnedX,pinnedY,map_pow,map_mul,map_inv,PresentedGroup.of] using h

theorem presentation_pair_closure : Subgroup.closure ({pinnedX,pinnedY} : Set Model)=⊤ := by
  apply top_unique
  rw [←PresentedGroup.closure_range_of {w | w∈relators}]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure (by simp [pinnedX])
  · exact Subgroup.subset_closure (by simp [pinnedY])

end SymmetricSubgroupAsymptotics.CFSGJankoOnePresentationGenerators
