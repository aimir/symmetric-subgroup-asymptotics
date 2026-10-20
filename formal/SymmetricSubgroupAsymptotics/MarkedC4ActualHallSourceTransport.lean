import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification
import SymmetricSubgroupAsymptotics.MarkedC4ActualOrderedSubdirectTransport

/-! Exact Hall fibre transport along the actual physical reordering.
The target, including its one global marker, is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHallSourceTransport

def homEquiv {B C T : Type} [Group B] [Group C] [Group T]
    (e : B ≃* C) : (B →* T) ≃ (C →* T) where
  toFun f := f.comp e.symm.toMonoidHom
  invFun f := f.comp e.toMonoidHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

def fibreEquiv (E : Type) [CommGroup E] {B C : Type} [Group B] [Group C]
    (e : B ≃* C) : AbelianProductGraphClassification.FullSecond E B ≃
      AbelianProductGraphClassification.FullSecond E C :=
  (AbelianProductGraphClassification.fullClassification (E := E) (B := B)).trans
    ((Equiv.sigmaCongrRight (fun _ => homEquiv e)).trans
      (AbelianProductGraphClassification.fullClassification (E := E) (B := C)).symm)

theorem fibre_card_eq (E : Type) [CommGroup E] {B C : Type} [Group B] [Group C]
    (e : B ≃* C) : Nat.card (AbelianProductGraphClassification.FullSecond E B)=
      Nat.card (AbelianProductGraphClassification.FullSecond E C) :=
  Nat.card_congr (fibreEquiv E e)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHallSourceTransport
