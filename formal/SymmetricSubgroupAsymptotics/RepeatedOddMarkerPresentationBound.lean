import SymmetricSubgroupAsymptotics.RepeatedOddMarkerPartitionSum
import SymmetricSubgroupAsymptotics.RepeatedCharacterPresentations
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted presentation upper bound for the original marker family

One canonical presentation is chosen for each original contraction image.
Its allocation fibres have exactly the original isotype weight. Summing
over a larger family of presentations therefore gives an upper bound for
the actual marker subgroup count. No division by label enumerations, and
no assertion that all presentations are distinct original images, is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerPresentationBound

open RepeatedCharacterCollapse RepeatedCharacterPartition RepeatedCharacterPresentations
open RepeatedOddMarkerIsotypeCount RepeatedOddMarkerPartitionSum
open DiagonalInvariantSubmodules DiagonalFullSubmoduleWeights TernaryFullWeightReindex

variable {ι D : Type} [Fintype ι] [Group D]

def allocationWeight {Q : Type} [Fintype Q] (f : ι → Q) : ℕ :=
  ∏ q : Q, ternaryFullWeight {i : ι // f i = q}

def presentationWeight (z : Presentation (ι := ι) (C := Sign) (D := D)) : ℕ :=
  allocationWeight z.2.1.1

def allocationFibreEquiv {Q : Type} (r : Setoid ι) (e : Quotient r ≃ Q)
    (q : Quotient r) :
    Fibre r q ≃ {i : ι // e (Quotient.mk r i) = e q} where
  toFun i := ⟨i.1, congrArg e i.2⟩
  invFun i := ⟨i.1, e.injective i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem allocationWeight_reindexed {Q : Type} [Fintype Q]
    (r : Setoid ι) (e : Quotient r ≃ Q) :
    allocationWeight (fun i => e (Quotient.mk r i)) = partitionWeight r := by
  symm
  exact Fintype.prod_equiv e _ _ (fun q => weight_eq (allocationFibreEquiv r e q))

theorem presentationWeight_present (B : Subgroup ((ι → Sign) × D)) :
    presentationWeight (present B) = partitionWeight (relation B) :=
  allocationWeight_reindexed (relation B) (Fintype.equivFin (Quotient (relation B)))

/-- Preserve nontriviality of every actual retained sign and every original
predicate through reconstruction. -/
def Admissible (P : Subgroup ((ι → Sign) × D) → Prop)
    (z : Presentation (ι := ι) (C := Sign) (D := D)) : Prop :=
  (∀ q, character z.2.2 q ≠ 1) ∧ P (original z)

theorem present_admissible (P : Subgroup ((ι → Sign) × D) → Prop)
    (B : RepeatedOddMarkerImageSum.ImageState P) : Admissible P (present B.1) := by
  constructor
  · apply (allocation_characters_nontrivial_iff (present B.1).2.1.1
      (present B.1).2.1.2 (present B.1).2.2).mp
    change ∀ i, character (original (present B.1)) i ≠ 1
    rw [original_present]
    exact B.2.1
  · simpa only [original_present] using B.2.2

/-- A structural inclusion on chosen actual presentations is enough. It
is not a premise about any subgroup count or final numerical sum. -/
def imageCoverEmbedding (P : Subgroup ((ι → Sign) × D) → Prop)
    (A : Presentation (ι := ι) (C := Sign) (D := D) → Prop)
    (hcover : ∀ B : RepeatedOddMarkerImageSum.ImageState P, A (present B.1)) :
    RepeatedOddMarkerImageSum.ImageState P ↪ {z // A z} where
  toFun B := ⟨present B.1, hcover B⟩
  inj' _ _ h := Subtype.ext (present_injective (congrArg Subtype.val h))

private theorem sum_embedding_le {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (w : B → ℕ) : (∑ a : A, w (e a)) ≤ ∑ b : B, w b := by
  calc
    (∑ a : A, w (e a)) = ∑ b ∈ Finset.univ.image e, w b := by
      rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    _ ≤ ∑ b : B, w b := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

section Finite

variable [Finite D]

local instance imageStateFinite (P : Subgroup ((ι → Sign) × D) → Prop) :
    Finite (RepeatedOddMarkerImageSum.ImageState P) :=
  Finite.of_injective (fun B : RepeatedOddMarkerImageSum.ImageState P => B.1)
    Subtype.val_injective

local instance imageStateFintype (P : Subgroup ((ι → Sign) × D) → Prop) :
    Fintype (RepeatedOddMarkerImageSum.ImageState P) := Fintype.ofFinite _

local instance coverFintype
    (A : Presentation (ι := ι) (C := Sign) (D := D) → Prop) :
    Fintype {z // A z} := Fintype.ofFinite _

/-- Bound the actual original whole-marker family by any structural
presentation cover, retaining its exact nonnegative allocation weights. -/
theorem card_family_le_cover (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop)
    (A : Presentation (ι := ι) (C := Sign) (D := D) → Prop)
    (hcover : ∀ B : RepeatedOddMarkerImageSum.ImageState P, A (present B.1)) :
    Nat.card (RepeatedOddMarkerImageSum.Family P) ≤
      ∑ z : {z // A z}, presentationWeight z.1 := by
  calc
    Nat.card (RepeatedOddMarkerImageSum.Family P) =
        ∑ B : RepeatedOddMarkerImageSum.ImageState P,
          ∏ a : Label (actualScalar B.1),
            ternaryFullWeight (Coordinate (actualScalar B.1) a) :=
      RepeatedOddMarkerImageSum.card_family hD P
    _ = ∑ B : RepeatedOddMarkerImageSum.ImageState P, presentationWeight (present B.1) := by
      apply Finset.sum_congr rfl
      intro B _
      exact (isotype_weight_eq_partitionWeight B.1).trans
        (presentationWeight_present B.1).symm
    _ ≤ ∑ z : {z // A z}, presentationWeight z.1 :=
      sum_embedding_le (imageCoverEmbedding P A hcover) (fun z => presentationWeight z.1)

theorem card_family_le_admissible (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop) :
    Nat.card (RepeatedOddMarkerImageSum.Family P) ≤
      ∑ z : {z // Admissible P z}, presentationWeight z.1 :=
  card_family_le_cover hD P (Admissible P) (present_admissible P)

theorem familyWeight_le_cover (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop)
    (A : Presentation (ι := ι) (C := Sign) (D := D) → Prop)
    (hcover : ∀ B : RepeatedOddMarkerImageSum.ImageState P, A (present B.1)) :
    RepeatedOddMarkerImageSum.familyWeight P ≤
      ∑ z : {z // A z}, (presentationWeight z.1 : ℚ) := by
  rw [← RepeatedOddMarkerImageSum.card_family_weight_rat hD P]
  exact_mod_cast card_family_le_cover hD P A hcover

end Finite

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerPresentationBound

end
