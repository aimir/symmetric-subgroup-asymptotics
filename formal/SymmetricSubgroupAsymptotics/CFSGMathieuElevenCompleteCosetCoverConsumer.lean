import SymmetricSubgroupAsymptotics.FinitePresentationCompleteCosetCover
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M11

/-! Conditional INTERNAL certificate consumer only. No complete720-edge
certificate is supplied here, and this is not an extra T1 input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenCompleteCosetCoverConsumer
open FinitePresentationCosetLink FinitePresentationCompleteCosetCover
abbrev G := CFSG.Models.Presentations.M11.Model
def generators (i : Fin 2) : G := PresentedGroup.of i
def periodElement : G := generators 0 * generators 1

theorem lift_generators : FreeGroup.lift generators =
    PresentedGroup.mk {w | w ∈ CFSG.Models.Presentations.M11.relators} := by
  apply FreeGroup.ext_hom
  intro i
  rfl

theorem eval_surjective : Function.Surjective (eval generators) := by
  intro z
  obtain ⟨w,rfl⟩ := PresentedGroup.mk_surjective
    {w | w ∈ CFSG.Models.Presentations.M11.relators} z
  refine Quot.inductionOn w ?_
  intro l
  refine ⟨l,?_⟩
  unfold eval
  rw [lift_generators]
  rfl

theorem period_eleven : periodElement^11=1 := by
  have hr : PresentedGroup.mk {w | w ∈ CFSG.Models.Presentations.M11.relators}
      ((FreeGroup.of (0 : Fin 2)*FreeGroup.of 1)^11)=1 :=
    PresentedGroup.one_of_mem (by simp [CFSG.Models.Presentations.M11.relators])
  simpa only [map_pow,map_mul,PresentedGroup.of,periodElement,generators] using hr

theorem finite_and_card_le_of_complete_cover (reps : Fin 720 → Word (Fin 2))
    (C : Certificate (Subgroup.zpowers periodElement) generators reps) :
    Finite G ∧ Nat.card G ≤ 7920 := by
  simpa only [show 11*720=7920 by decide] using
    cyclic_finite_and_card_le generators reps periodElement (by decide : 0<11)
      period_eleven C eval_surjective

theorem index_le_of_complete_cover (reps : Fin 720 → Word (Fin 2))
    (C : Certificate (Subgroup.zpowers periodElement) generators reps) :
    (Subgroup.zpowers periodElement).index ≤ 720 :=
  index_le _ generators reps C eval_surjective

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenCompleteCosetCoverConsumer
