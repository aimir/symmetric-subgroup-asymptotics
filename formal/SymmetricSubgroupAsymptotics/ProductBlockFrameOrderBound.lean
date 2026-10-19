import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding
import SymmetricSubgroupAsymptotics.ActualThreeByTwoWreathCard

/-! Order bounds from the actual product frame, without enumerating the
original group or its normal subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F : Type} [Finite X] [Finite I] [Finite F]
    {U : Subgroup (Equiv.Perm X)} (C : ProductBlockFrame U I F)

include C
theorem card_le_factorial_wreath :
    Nat.card U ≤ (Nat.card F).factorial^Nat.card I*(Nat.card I).factorial := by
  let W := PermutationalWreathProduct (Equiv.Perm F) (Equiv.Perm I) I
  letI : Finite W := Finite.of_equiv ((I → Equiv.Perm F) × Equiv.Perm I)
    PermutationalWreathProduct.coordinateEquiv.symm
  have h := Nat.card_le_card_of_injective C.wreathEmbedding C.wreathEmbedding_injective
  change Nat.card U ≤ Nat.card W at h
  simpa only [W,PermutationalWreathProduct.natCard,Nat.card_perm] using h

theorem quartet_order_le (hi : Nat.card I=4) (hf : Nat.card F=4) :
    Nat.card U≤2^32 := by
  have h := C.card_le_factorial_wreath
  rw [hi,hf] at h
  exact h.trans (by norm_num)

theorem two_eight_order_le (hi : Nat.card I=2) (hf : Nat.card F=8) :
    Nat.card U≤2^32 := by
  have h := C.card_le_factorial_wreath
  rw [hi,hf] at h
  exact h.trans (by norm_num)

end SymmetricSubgroupAsymptotics.ProductBlockFrame
