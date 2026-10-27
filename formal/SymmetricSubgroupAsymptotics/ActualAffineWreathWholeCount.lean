import SymmetricSubgroupAsymptotics.ActualFullWreathSmallBaseCount
import SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleWholeCount
import SymmetricSubgroupAsymptotics.PrimitiveAffineUniformLocalCharge

/-! Actual affine primitive-local whole-family envelope: the checked
binary local-order estimate pays ALL base kernels and whole top lifts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualAffineWreathWholeCount
variable {R X Q I : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
    [FaithfulSMul R X] [Group Q] [Finite Q] [MulAction Q I] [Finite I]

theorem card_family_le (P : PrimitiveAffineProfile R X) (x : X) :
    let a := (Nat.log 2 (Nat.card X)+1)^2
    let q := MarkedC4.genRank Q
    Nat.card (ActualFullWreathFamily.Family R Q I)≤
      2^((Nat.card I*a)*(Nat.card I*a))*Nat.card R^(Nat.card I*q) := by
  dsimp only
  obtain ⟨f,hf⟩ := ActualFullWreathSemisimpleWholeCount.exists_tuple
    (MarkedC4.genRank Q) (le_refl _)
  exact ActualFullWreathSmallBaseCount.card_family_le _
    (PrimitiveAffineUniformLocalCharge.card_le_binary_log_square P x) f hf

end SymmetricSubgroupAsymptotics.ActualAffineWreathWholeCount
