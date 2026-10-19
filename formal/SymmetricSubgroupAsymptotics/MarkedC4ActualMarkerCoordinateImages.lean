import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! The marker factors for RDT4.6 are actual coordinate IMAGES, so vertical
markers and proper marker projections are both allowed. Their cutoff is
four, independently of the number of global marker coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkerCoordinateImages
open ActualGlobalMarkGeneratorRank ActualMarkZeroNormalRank

abbrev C4 := Multiplicative (ZMod 4)

def coordinate (r : ℕ) (i : Fin r) : Marks r →* C4 where
  toFun x := Multiplicative.ofAdd (x.toAdd i)
  map_one' := rfl
  map_mul' _ _ := rfl

variable {B : Type} [Group B] (r : ℕ) (A : Subgroup (B × Marks r))

def actualCoordinate (i : Fin r) : A →* C4 := (coordinate r i).comp (mark A)
abbrev Factor (i : Fin r) := (actualCoordinate r A i).range

def ontoFactor (i : Fin r) : A →* Factor r A i :=
  (actualCoordinate r A i).rangeRestrict

theorem ontoFactor_surjective (i : Fin r) : Function.Surjective (ontoFactor r A i) :=
  (actualCoordinate r A i).rangeRestrict_surjective

theorem factor_card_le_four (i : Fin r) : Nat.card (Factor r A i)≤4 := by
  have h := Nat.card_le_card_of_injective (Factor r A i).subtype Subtype.val_injective
  simpa only [C4,Nat.card_congr Multiplicative.toAdd,Nat.card_zmod] using h

theorem factor_binary (i : Fin r) : IsPGroup 2 (Factor r A i) := by
  have h : IsPGroup 2 C4 := by
    apply IsPGroup.of_card (n := 2)
    simp only [C4,Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
    norm_num
  exact h.to_subgroup (Factor r A i)

/-- The marker factors never require a cutoff depending on r. -/
theorem factor_card_le_cutoff (k : ℕ) (hk : 2≤k) (i : Fin r) :
    Nat.card (Factor r A i)≤2^k := by
  apply (factor_card_le_four r A i).trans
  calc
    4=(2 : ℕ)^2 := by norm_num
    _≤2^k := Nat.pow_le_pow_right (by omega) hk

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkerCoordinateImages
