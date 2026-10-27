import SymmetricSubgroupAsymptotics.CFSGHeldTauCetiPresentationCore
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.He
import Mathlib.Tactic.Tauto

/-!
Literal presentation transport only. The TauCeti carrier in the imported
minimal port is defined by the seven words of its pinned He row. Neither
finiteness, simplicity, order, nor a concrete He recognition result is used.
-/

namespace SymmetricSubgroupAsymptotics.CFSGHeldTauCetiPresentationEquiv

open TauCeti

/-- Equality of defining relation sets transports their quotients identically. -/
def equivOfRelatorSetEq {α : Type*} {s t : Set (FreeGroup α)} (h : s = t) :
    PresentedGroup s ≃* PresentedGroup t := by
  subst t
  exact MulEquiv.refl _

@[simp] theorem equivOfRelatorSetEq_apply_of {α : Type*}
    {s t : Set (FreeGroup α)} (h : s = t) (i : α) :
    equivOfRelatorSetEq h (PresentedGroup.of i) = PresentedGroup.of i := by
  subst t
  rfl

@[simp] theorem equivOfRelatorSetEq_symm_apply_of {α : Type*}
    {s t : Set (FreeGroup α)} (h : s = t) (i : α) :
    (equivOfRelatorSetEq h).symm (PresentedGroup.of i) = PresentedGroup.of i := by
  subst t
  rfl

/-- The same seven words occur, with source positions four and six exchanged. -/
theorem interpreted_relatorSet_eq_old :
    {w | w ∈ Sporadic.hePresentation.transcribed.map Relator.toFreeGroup} =
      {w | w ∈ CFSG.Models.Presentations.He.relators} := by
  have hp : (Sporadic.hePresentation.transcribed.map Relator.toFreeGroup).Perm
      CFSG.Models.Presentations.He.relators := by
    simp only [Sporadic.hePresentation, List.map_cons, List.map_nil,
      Relator.toFreeGroup_pow, Relator.toFreeGroup_commInvInv,
      Relator.toFreeGroup_mul, Relator.toFreeGroup_inv, Relator.toFreeGroup_gen,
      CFSG.Models.Presentations.He.relators, CFSG.Models.commWord, pow_one, mul_assoc]
    apply List.Perm.cons
    apply List.Perm.cons
    apply List.Perm.cons
    exact (List.Perm.swap _ _ _).trans
      ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans (List.Perm.swap _ _ _))
  ext w
  exact hp.mem_iff

/-- Compilation preserves the literal relation set; relation order is irrelevant. -/
theorem relatorSet_eq_old :
    Sporadic.hePresentation.relatorSet =
      {w | w ∈ CFSG.Models.Presentations.He.relators} := by
  have hc : Sporadic.hePresentation.relators.map FreeGroup.mk =
      Sporadic.hePresentation.transcribed.map Relator.toFreeGroup := by
    rw [GroupPresentation.relators_def, List.map_map]
    congr 1
    funext r
    exact Relator.toWord_toFreeGroup r
  change {w | w ∈ Sporadic.hePresentation.relators.map FreeGroup.mk} = _
  rw [hc]
  exact interpreted_relatorSet_eq_old

/-- The old pinned carrier and the pinned TauCeti carrier have identical generators. -/
def oldEquivTauCeti : CFSG.Models.Presentations.He.Model ≃*
    GroupPresentation.Group Sporadic.hePresentation :=
  equivOfRelatorSetEq relatorSet_eq_old.symm

@[simp] theorem oldEquivTauCeti_apply_of (i : Fin 2) :
    oldEquivTauCeti (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_apply_of relatorSet_eq_old.symm i

@[simp] theorem oldEquivTauCeti_symm_apply_of (i : Fin 2) :
    oldEquivTauCeti.symm (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_symm_apply_of relatorSet_eq_old.symm i

end SymmetricSubgroupAsymptotics.CFSGHeldTauCetiPresentationEquiv
