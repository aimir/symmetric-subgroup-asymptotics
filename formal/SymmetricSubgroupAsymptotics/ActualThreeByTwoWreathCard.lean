import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Index

/-! A faithful original three-by-two block action has group order dividing
72. This is a divisibility statement from its actual wreath embedding,
not a bound inherited by arbitrary subgroup normal generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

namespace PermutationalWreathProduct
variable {D Q I : Type} [Group D] [Group Q] [MulAction Q I]

def coordinateEquiv : PermutationalWreathProduct D Q I ≃ (I → D) × Q where
  toFun a := (a.left,a.right)
  invFun a := ⟨a.1,a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard [Finite I] :
    Nat.card (PermutationalWreathProduct D Q I) = Nat.card D ^ Nat.card I * Nat.card Q := by
  rw [Nat.card_congr coordinateEquiv,Nat.card_prod,Nat.card_fun]
end PermutationalWreathProduct

variable {G X I : Type} [Group G] [Finite G] [Finite X] [Finite I]
    [MulAction G X] [MulAction G I] [MulAction.IsPretransitive G I]
    [FaithfulSMul G X]
    (b : X → I) (hb : ∀ (g : G) (x : X), b (g • x) = g • b x)
    (i₀ : I)

include hb in
/-- The actual local component and actual top both embed in the full
small symmetric groups; the full original action embeds in their wreath. -/
theorem actual_threeByTwo_card_dvd
    (hI : Nat.card I = 2) (hF : Nat.card (originalBlockFibre b i₀) = 3) :
    Nat.card G ∣ 72 := by
  classical
  let C := ActualBlockWreathEmbedding.Component b hb i₀
  let T := ActualBlockWreathEmbedding.Top (A := G) (X := I)
  let W := PermutationalWreathProduct C T I
  letI : Finite W := Finite.of_equiv ((I → C) × T)
    (PermutationalWreathProduct.coordinateEquiv.symm)
  have hC : Nat.card C ∣ 6 := by
    have h := Subgroup.card_dvd_of_injective
      (C.subtype) (show Function.Injective C.subtype from Subtype.val_injective)
    have hc : Nat.card (Equiv.Perm (originalBlockFibre b i₀)) = 6 := by
      letI := Fintype.ofFinite (originalBlockFibre b i₀)
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,← Nat.card_eq_fintype_card,hF]
      decide +kernel
    exact hc ▸ h
  have hT : Nat.card T ∣ 2 := by
    have h := Subgroup.card_dvd_of_injective
      (T.subtype) (show Function.Injective T.subtype from Subtype.val_injective)
    have ht : Nat.card (Equiv.Perm I) = 2 := by
      letI := Fintype.ofFinite I
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,← Nat.card_eq_fintype_card,hI]
      decide +kernel
    exact ht ▸ h
  have hG : Nat.card G ∣ Nat.card W := Subgroup.card_dvd_of_injective
    (ActualBlockWreathEmbedding.embedding b hb i₀)
    (ActualBlockWreathEmbedding.embedding_injective b hb i₀)
  have hW : Nat.card W ∣ 72 := by
    change Nat.card (PermutationalWreathProduct C T I) ∣ 72
    rw [PermutationalWreathProduct.natCard,hI]
    exact (Nat.mul_dvd_mul (pow_dvd_pow_of_dvd hC 2) hT)
  exact hG.trans hW

end SymmetricSubgroupAsymptotics
end
