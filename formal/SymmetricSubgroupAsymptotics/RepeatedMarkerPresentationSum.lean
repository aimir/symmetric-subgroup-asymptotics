import SymmetricSubgroupAsymptotics.RepeatedOddMarkerPresentationBound
import SymmetricSubgroupAsymptotics.RepeatedMarkerAllocationWeights

/-!
# Separate the allocation sum from the actual collapsed-model count

After an enlarged presentation predicate depends only on the retained
width and the actual collapsed subgroup, the allocation sum factors from
the subgroup count. Both finite families are the complete literal ones.
For original positions `Fin g`, the checked allocation theorem supplies
the exact factor `g! H` without any division by retained-label orderings.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerPresentationSum

open RepeatedCharacterPresentations RepeatedOddMarkerPartitionSum
open RepeatedOddMarkerPresentationBound

variable {ι D : Type} [Fintype ι] [Group D] [Finite D]

abbrev Width := Fin (Fintype.card ι + 1)
abbrev Allocation (q : ℕ) := {f : ι → Fin q // Function.Surjective f}

local instance allocationFintype (q : ℕ) : Fintype (Allocation (ι := ι) q) :=
  Fintype.ofFinite _

def allocationSum (q : ℕ) : ℚ :=
  ∑ f : Allocation (ι := ι) q, (allocationWeight f.1 : ℚ)

variable (S : ∀ q : Width (ι := ι), Subgroup ((Fin q.1 → Sign) × D) → Prop)

abbrev Model (q : Width (ι := ι)) :=
  {Y : Subgroup ((Fin q.1 → Sign) × D) // S q Y}

def Cover :=
  {z : Presentation (ι := ι) (C := Sign) (D := D) // S z.1 z.2.2}

local instance modelFinite (q : Width (ι := ι)) : Finite (Model S q) :=
  Finite.of_injective (fun Y : Model S q => (Y.1 : Set ((Fin q.1 → Sign) × D)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance modelFintype (q : Width (ι := ι)) : Fintype (Model S q) :=
  Fintype.ofFinite _

local instance coverFinite : Finite (Cover S) :=
  Finite.of_injective (fun z : Cover S => z.1) Subtype.val_injective

local instance coverFintype : Fintype (Cover S) := Fintype.ofFinite _

/-- Reorder the parameters while retaining the actual collapsed Y and
the same allocation. There is no quotient of presentations here. -/
def splitEquiv : Cover S ≃
    (Σ q : Width (ι := ι), Allocation (ι := ι) q.1 × Model S q) where
  toFun z := ⟨z.1.1, z.1.2.1, ⟨z.1.2.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1, z.2.2.1⟩, z.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact factorization after allocation-dependent restrictions have been
removed. The second factor is the actual permitted subgroup cardinality. -/
theorem sum_cover_eq :
    (∑ z : Cover S, (presentationWeight z.1 : ℚ)) =
      ∑ q : Width (ι := ι), allocationSum (ι := ι) q.1 * (Nat.card (Model S q) : ℚ) := by
  calc
    (∑ z : Cover S, (presentationWeight z.1 : ℚ)) =
        ∑ z : (Σ q : Width (ι := ι), Allocation (ι := ι) q.1 × Model S q),
          (allocationWeight z.2.1.1 : ℚ) :=
      Fintype.sum_equiv (splitEquiv S) _ _ (fun _ => rfl)
    _ = ∑ q : Width (ι := ι),
        ∑ f : Allocation (ι := ι) q.1, ∑ _Y : Model S q, (allocationWeight f.1 : ℚ) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      exact Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, Nat.card_eq_fintype_card]
      exact mul_comm _ _

theorem familyWeight_le_factored (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Sign) × D) → Prop)
    (hcover : ∀ B : RepeatedOddMarkerImageSum.ImageState P,
      S (present B.1).1 (present B.1).2.2) :
    RepeatedOddMarkerImageSum.familyWeight P ≤
      ∑ q : Width (ι := ι), allocationSum (ι := ι) q.1 * (Nat.card (Model S q) : ℚ) := by
  calc
    RepeatedOddMarkerImageSum.familyWeight P ≤
        ∑ z : Cover S, (presentationWeight z.1 : ℚ) :=
      familyWeight_le_cover hD P (fun z => S z.1 z.2.2) hcover
    _ = _ := sum_cover_eq S

/-- The exact original marker-allocation factor on the canonical retained
coordinate set Fin q. No Y-cardinality estimate enters this identity. -/
theorem allocationSum_fin_eq (g q : ℕ) :
    allocationSum (ι := Fin g) q =
      (g.factorial : ℚ) * RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q) g := by
  simpa only [allocationSum, allocationWeight, Nat.cast_prod] using
    RepeatedMarkerAllocationWeights.literal_fibre_sum_eq (Q := Fin q) g

end SymmetricSubgroupAsymptotics.RepeatedMarkerPresentationSum

end
