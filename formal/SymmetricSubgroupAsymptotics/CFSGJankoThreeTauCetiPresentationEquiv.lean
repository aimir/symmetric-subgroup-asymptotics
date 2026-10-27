import SymmetricSubgroupAsymptotics.CFSGJankoThreeTauCetiPresentationCore
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J3

/-!
Literal presentation transport only. The TauCeti carrier in the imported
minimal port is defined by the eight words of its pinned J3 row. Neither
finiteness, simplicity, order, nor a concrete J3 recognition result is used.
-/

namespace SymmetricSubgroupAsymptotics.CFSGJankoThreeTauCetiPresentationEquiv

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

/-- Structural interpretation matches all eight old relators, in source order. -/
theorem interpreted_relators_eq_old :
    Sporadic.j3Presentation.transcribed.map Relator.toFreeGroup =
      CFSG.Models.Presentations.J3.relators := by
  simp only [Sporadic.j3Presentation, List.map_cons, List.map_nil,
    Relator.toFreeGroup_pow, Relator.toFreeGroup_commInvInv,
    Relator.toFreeGroup_mul, Relator.toFreeGroup_inv, Relator.toFreeGroup_gen,
    CFSG.Models.Presentations.J3.relators, CFSG.Models.commWord, pow_one, mul_assoc]

/-- The actual compiled-word compiler has the same free-group elements. -/
theorem compiled_relators_eq_old :
    Sporadic.j3Presentation.relators.map FreeGroup.mk =
      CFSG.Models.Presentations.J3.relators := by
  calc
    Sporadic.j3Presentation.relators.map FreeGroup.mk =
        Sporadic.j3Presentation.transcribed.map Relator.toFreeGroup := by
      rw [GroupPresentation.relators_def, List.map_map]
      congr 1
      funext r
      exact Relator.toWord_toFreeGroup r
    _ = _ := interpreted_relators_eq_old

/-- No normal-closure argument is hidden here: the defining sets themselves agree. -/
theorem relatorSet_eq_old :
    Sporadic.j3Presentation.relatorSet =
      {w | w ∈ CFSG.Models.Presentations.J3.relators} := by
  change {w | w ∈ Sporadic.j3Presentation.relators.map FreeGroup.mk} = _
  rw [compiled_relators_eq_old]
  rfl

/-- The old pinned carrier and the pinned TauCeti carrier have identical generators. -/
def oldEquivTauCeti : CFSG.Models.Presentations.J3.Model ≃*
    GroupPresentation.Group Sporadic.j3Presentation :=
  equivOfRelatorSetEq relatorSet_eq_old.symm

@[simp] theorem oldEquivTauCeti_apply_of (i : Fin 2) :
    oldEquivTauCeti (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_apply_of relatorSet_eq_old.symm i

@[simp] theorem oldEquivTauCeti_symm_apply_of (i : Fin 2) :
    oldEquivTauCeti.symm (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_symm_apply_of relatorSet_eq_old.symm i

end SymmetricSubgroupAsymptotics.CFSGJankoThreeTauCetiPresentationEquiv
