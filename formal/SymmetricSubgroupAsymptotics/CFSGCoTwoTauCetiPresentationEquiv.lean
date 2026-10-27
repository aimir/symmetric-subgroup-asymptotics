import SymmetricSubgroupAsymptotics.CFSGCoTwoTauCetiPresentationCore
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.Co2

/-!
Literal presentation transport only. The TauCeti carrier in the imported
minimal port is defined by the ten words of its pinned Co2 row. Neither
finiteness, simplicity, order, nor a concrete Co2 recognition result is used.
-/

namespace SymmetricSubgroupAsymptotics.CFSGCoTwoTauCetiPresentationEquiv

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

/-- Structural interpretation matches all ten old relators, in source order. -/
theorem interpreted_relators_eq_old :
    Sporadic.co2Presentation.transcribed.map Relator.toFreeGroup =
      CFSG.Models.Presentations.Co2.relators := by
  simp only [Sporadic.co2Presentation, List.map_cons, List.map_nil,
    Relator.toFreeGroup_pow, Relator.toFreeGroup_commInvInv,
    Relator.toFreeGroup_mul, Relator.toFreeGroup_inv, Relator.toFreeGroup_gen,
    CFSG.Models.Presentations.Co2.relators, CFSG.Models.commWord, pow_one, mul_assoc]

/-- The actual compiled-word compiler has the same free-group elements. -/
theorem compiled_relators_eq_old :
    Sporadic.co2Presentation.relators.map FreeGroup.mk =
      CFSG.Models.Presentations.Co2.relators := by
  calc
    Sporadic.co2Presentation.relators.map FreeGroup.mk =
        Sporadic.co2Presentation.transcribed.map Relator.toFreeGroup := by
      rw [GroupPresentation.relators_def, List.map_map]
      congr 1
      funext r
      exact Relator.toWord_toFreeGroup r
    _ = _ := interpreted_relators_eq_old

/-- No normal-closure argument is hidden here: the defining sets themselves agree. -/
theorem relatorSet_eq_old :
    Sporadic.co2Presentation.relatorSet =
      {w | w ∈ CFSG.Models.Presentations.Co2.relators} := by
  change {w | w ∈ Sporadic.co2Presentation.relators.map FreeGroup.mk} = _
  rw [compiled_relators_eq_old]
  rfl

/-- The old pinned carrier and the pinned TauCeti carrier have identical generators. -/
def oldEquivTauCeti : CFSG.Models.Presentations.Co2.Model ≃*
    GroupPresentation.Group Sporadic.co2Presentation :=
  equivOfRelatorSetEq relatorSet_eq_old.symm

@[simp] theorem oldEquivTauCeti_apply_of (i : Fin 2) :
    oldEquivTauCeti (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_apply_of relatorSet_eq_old.symm i

@[simp] theorem oldEquivTauCeti_symm_apply_of (i : Fin 2) :
    oldEquivTauCeti.symm (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_symm_apply_of relatorSet_eq_old.symm i

end SymmetricSubgroupAsymptotics.CFSGCoTwoTauCetiPresentationEquiv
