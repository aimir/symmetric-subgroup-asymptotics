import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTauCetiPresentationCore
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M24

/-!
Literal presentation transport only. The TauCeti carrier in the imported
minimal port is defined by the 7 words of its pinned M24 row. Neither
finiteness, simplicity, order, nor a concrete M24 recognition result is used.
-/

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTauCetiPresentationEquiv

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

/-- Structural interpretation matches all 7 old relators, in source order. -/
theorem interpreted_relators_eq_old :
    Sporadic.m24Presentation.transcribed.map Relator.toFreeGroup =
      CFSG.Models.Presentations.M24.relators := by
  simp only [Sporadic.m24Presentation, List.map_cons, List.map_nil,
    Relator.toFreeGroup_pow, Relator.toFreeGroup_commInvInv,
    Relator.toFreeGroup_mul, Relator.toFreeGroup_inv, Relator.toFreeGroup_gen,
    CFSG.Models.Presentations.M24.relators, CFSG.Models.commWord, pow_one, mul_assoc]

/-- The actual compiled-word compiler has the same free-group elements. -/
theorem compiled_relators_eq_old :
    Sporadic.m24Presentation.relators.map FreeGroup.mk =
      CFSG.Models.Presentations.M24.relators := by
  calc
    Sporadic.m24Presentation.relators.map FreeGroup.mk =
        Sporadic.m24Presentation.transcribed.map Relator.toFreeGroup := by
      rw [GroupPresentation.relators_def, List.map_map]
      congr 1
      funext r
      exact Relator.toWord_toFreeGroup r
    _ = _ := interpreted_relators_eq_old

/-- No normal-closure argument is hidden here: the defining sets themselves agree. -/
theorem relatorSet_eq_old :
    Sporadic.m24Presentation.relatorSet =
      {w | w ∈ CFSG.Models.Presentations.M24.relators} := by
  change {w | w ∈ Sporadic.m24Presentation.relators.map FreeGroup.mk} = _
  rw [compiled_relators_eq_old]
  rfl

/-- The old pinned carrier and the pinned TauCeti carrier have identical generators. -/
def oldEquivTauCeti : CFSG.Models.Presentations.M24.Model ≃*
    GroupPresentation.Group Sporadic.m24Presentation :=
  equivOfRelatorSetEq relatorSet_eq_old.symm

@[simp] theorem oldEquivTauCeti_apply_of (i : Fin 2) :
    oldEquivTauCeti (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_apply_of relatorSet_eq_old.symm i

@[simp] theorem oldEquivTauCeti_symm_apply_of (i : Fin 2) :
    oldEquivTauCeti.symm (PresentedGroup.of i) = PresentedGroup.of i :=
  equivOfRelatorSetEq_symm_apply_of relatorSet_eq_old.symm i

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTauCetiPresentationEquiv
