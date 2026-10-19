import SymmetricSubgroupAsymptotics.DihedralEightRegularKleinBlockModel
import SymmetricSubgroupAsymptotics.CardEightPermutationConjugacy
import Mathlib.Data.Fintype.EquivFin

/-! The checked faithful D8 block action, as an actual subgroup of S4.
This is the canonical target for structural Sylow conjugacy. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.DihedralEightFourPointImage
open DihedralEightRegularKleinBlockModel
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

def label : R ≃ Fin 4 := Fintype.equivFinOfCardEq (by decide +kernel)

def actionFin : Q →* Equiv.Perm (Fin 4) :=
  label.permCongrHom.toMonoidHom.comp action

theorem actionFin_injective : Function.Injective actionFin := by
  intro q r h
  apply action_injective
  exact label.permCongrHom.injective h

def imageEquiv : Q ≃* actionFin.range :=
  MulEquiv.ofBijective actionFin.rangeRestrict
    ⟨fun _ _ h => actionFin_injective (congrArg Subtype.val h),
      actionFin.rangeRestrict_surjective⟩

theorem image_card : Nat.card actionFin.range=8 := by
  rw [← Nat.card_congr imageEquiv.toEquiv]
  exact DihedralGroup.nat_card.trans (by norm_num)

@[simp] theorem actionFin_label (q : Q) (r : R) :
    actionFin q (label r)=label (q • r) := by
  change label (action q (label.symm (label r)))=label (q • r)
  rw [label.symm_apply_apply]
  rfl

/-- Every actual order-eight block image has a physical conjugator to D8. -/
theorem exists_conjugator (B : Subgroup (Equiv.Perm (Fin 4)))
    (hB : Nat.card B=8) :
    ∃ g : Equiv.Perm (Fin 4), MulAut.conj g • B=actionFin.range :=
  CardEightPermutationConjugacy.exists_conjugator B actionFin.range hB image_card
end SymmetricSubgroupAsymptotics.DihedralEightFourPointImage
