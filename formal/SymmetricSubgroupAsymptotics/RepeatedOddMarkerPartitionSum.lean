import SymmetricSubgroupAsymptotics.RepeatedCharacterPartition
import SymmetricSubgroupAsymptotics.RepeatedOddMarkerImageSum
import SymmetricSubgroupAsymptotics.TernaryFullWeightReindex

/-!
# Exact marker model sum over canonical collapsed images

The original image sum is reindexed by the literal equality partition of
its coordinate characters and the distinct-coordinate image on that
partition. Each factor uses the entire corresponding original coordinate
fibre. The predicate is evaluated on the reconstructed original image.

No ordering of the retained characters, additional factorial, or physical
normalizer quotient is introduced by this model-level reindexing.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerPartitionSum

open RepeatedCharacterPartition RepeatedCharacterCollapse
open RepeatedOddMarkerIsotypeCount DiagonalInvariantSubmodules
open DiagonalFullSubmoduleWeights TernaryFullWeightReindex

variable {ι D : Type} [Fintype ι] [Group D]

abbrev Sign := Multiplicative (ZMod 2)

/-- The literal original coordinates belonging to one quotient class. -/
abbrev Fibre (r : Setoid ι) (q : Quotient r) :=
  {i : ι // Quotient.mk r i = q}

theorem allocation_surjective (r : Setoid ι) :
    Function.Surjective (Quotient.mk r) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro i
  exact ⟨i, rfl⟩

def allocationEquiv (r : Setoid ι) : ι ≃ Σ q : Quotient r, Fibre r q where
  toFun i := ⟨Quotient.mk r i, i, rfl⟩
  invFun i := i.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨q, i, hi⟩
    cases hi
    rfl

theorem fibre_card_pos (r : Setoid ι) (q : Quotient r) :
    0 < Fintype.card (Fibre r q) := by
  obtain ⟨i, hi⟩ := allocation_surjective r q
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

theorem sum_fibre_card (r : Setoid ι) :
    (∑ q : Quotient r, Fintype.card (Fibre r q)) = Fintype.card ι := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (allocationEquiv r)).symm

def partitionWeight (r : Setoid ι) : ℕ :=
  ∏ q : Quotient r, ternaryFullWeight (Fibre r q)

theorem partitionWeight_eq_factors (r : Setoid ι) :
    partitionWeight r =
      ∏ q : Quotient r, ternaryFullFactor (Fintype.card (Fibre r q)) := by
  apply Finset.prod_congr rfl
  intro q _
  exact weight_eq_factor (Fibre r q)

/-- The quotient partition agrees with equality of the actual scalar
sign labels, including all correlations on the original image. -/
def scalarLabelEquiv (B : Subgroup ((ι → Sign) × D)) :
    Quotient (relation B) ≃ Label (actualScalar B) :=
  (Quotient.congrRight (fun i j => (actualScalar_eq_iff B i j).symm)).trans
    (Setoid.quotientKerEquivRange (actualScalar B))

@[simp] theorem scalarLabelEquiv_mk (B : Subgroup ((ι → Sign) × D)) (i : ι) :
    scalarLabelEquiv B (Quotient.mk (relation B) i) =
      DiagonalIsotypeProjection.coordinateLabel (actualScalar B) i := by
  apply Subtype.ext
  rfl

/-- Reindexing fixes each original coordinate; it changes only the
description of its actual equality class. -/
def scalarFibreEquiv (B : Subgroup ((ι → Sign) × D))
    (q : Quotient (relation B)) :
    Fibre (relation B) q ≃ Coordinate (actualScalar B) (scalarLabelEquiv B q) where
  toFun i := ⟨i.1, by
    have h := congrArg (scalarLabelEquiv B) i.2
    exact congrArg Subtype.val h⟩
  invFun i := ⟨i.1, (scalarLabelEquiv B).injective (by
    apply Subtype.ext
    exact i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem isotype_weight_eq_partitionWeight (B : Subgroup ((ι → Sign) × D)) :
    (∏ a : Label (actualScalar B),
      ternaryFullWeight (Coordinate (actualScalar B) a)) =
      partitionWeight (relation B) := by
  symm
  exact Fintype.prod_equiv (scalarLabelEquiv B) _ _
    (fun q => weight_eq (scalarFibreEquiv B q))

/-- Canonical collapsed images whose retained actual signs are nontrivial.
P remains a predicate on the original expanded subgroup, not on a chosen
presentation of the retained labels. -/
def State (P : Subgroup ((ι → Sign) × D) → Prop) :=
  {z : RepeatedCharacterPartition.Data (ι := ι) (C := Sign) (D := D) //
    (∀ q, character z.2.1 q ≠ 1) ∧ P (decode z)}

def imageStateEquiv (P : Subgroup ((ι → Sign) × D) → Prop) :
    RepeatedOddMarkerImageSum.ImageState P ≃ State P where
  toFun B := ⟨encode B.1,
    (expanded_characters_nontrivial_iff (relation B.1) (collapsed B.1)).mp
      (by
        change ∀ i, character (RepeatedCharacterPartition.decode
          (RepeatedCharacterPartition.encode B.1)) i ≠ 1
        rw [RepeatedCharacterPartition.decode_encode]
        exact B.2.1),
    by simpa only [RepeatedCharacterPartition.decode_encode] using B.2.2⟩
  invFun z := ⟨decode z.1,
    (expanded_characters_nontrivial_iff z.1.1 z.1.2.1).mpr z.2.1, z.2.2⟩
  left_inv B := Subtype.ext (RepeatedCharacterPartition.decode_encode B.1)
  right_inv z := Subtype.ext
    ((RepeatedCharacterPartition.equiv (ι := ι) (C := Sign) (D := D)).apply_symm_apply z.1)

@[simp] theorem imageStateEquiv_decode (P : Subgroup ((ι → Sign) × D) → Prop)
    (B : RepeatedOddMarkerImageSum.ImageState P) :
    decode (imageStateEquiv P B).1 = B.1 := RepeatedCharacterPartition.decode_encode B.1

/-- Every selected collapsed group is genuinely binary whenever the
original exterior is binary. -/
theorem state_isPGroup (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop) (z : State P) :
    IsPGroup 2 z.1.2.1 :=
  (expanded_isPGroup_iff z.1.1 z.1.2.1 2).mp
    (RepeatedOddMarkerImageSum.image_isPGroup hD (decode z.1))

section Finite

variable [Finite D]

local instance imageStateFinite (P : Subgroup ((ι → Sign) × D) → Prop) :
    Finite (RepeatedOddMarkerImageSum.ImageState P) :=
  Finite.of_injective (fun B : RepeatedOddMarkerImageSum.ImageState P => B.1)
    Subtype.val_injective

local instance imageStateFintype (P : Subgroup ((ι → Sign) × D) → Prop) :
    Fintype (RepeatedOddMarkerImageSum.ImageState P) := Fintype.ofFinite _

local instance stateFinite (P : Subgroup ((ι → Sign) × D) → Prop) : Finite (State P) :=
  Finite.of_injective (fun z : State P => decode z.1)
    (fun _ _ h => Subtype.ext (decode_injective h))

local instance stateFintype (P : Subgroup ((ι → Sign) × D) → Prop) :
    Fintype (State P) := Fintype.ofFinite _

/-- Exact whole-model count, with the canonical repeated-character
allocation retained. This is not a quotient of fixed-image fibres by a
physical occurrence-permutation action. -/
theorem card_family (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop) :
    Nat.card (RepeatedOddMarkerImageSum.Family P) =
      ∑ z : State P, partitionWeight z.1.1 := by
  calc
    Nat.card (RepeatedOddMarkerImageSum.Family P) =
        ∑ B : RepeatedOddMarkerImageSum.ImageState P,
          ∏ a : Label (actualScalar B.1),
            ternaryFullWeight (Coordinate (actualScalar B.1) a) :=
      RepeatedOddMarkerImageSum.card_family hD P
    _ = ∑ B : RepeatedOddMarkerImageSum.ImageState P,
        partitionWeight (relation B.1) := by
      apply Finset.sum_congr rfl
      intro B _
      exact isotype_weight_eq_partitionWeight B.1
    _ = ∑ z : State P, partitionWeight z.1.1 :=
      Fintype.sum_equiv (imageStateEquiv P) _ _ (fun _ => rfl)

theorem card_family_factors (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop) :
    Nat.card (RepeatedOddMarkerImageSum.Family P) =
      ∑ z : State P, ∏ q : Quotient z.1.1,
        ternaryFullFactor (Fintype.card (Fibre z.1.1 q)) := by
  rw [card_family hD P]
  apply Finset.sum_congr rfl
  intro z _
  exact partitionWeight_eq_factors z.1.1

theorem card_family_rat (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop) :
    (Nat.card (RepeatedOddMarkerImageSum.Family P) : ℚ) =
      ∑ z : State P, ∏ q : Quotient z.1.1,
        (ternaryFullFactor (Fintype.card (Fibre z.1.1 q)) : ℚ) := by
  exact_mod_cast card_family_factors hD P

end Finite

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerPartitionSum

end
