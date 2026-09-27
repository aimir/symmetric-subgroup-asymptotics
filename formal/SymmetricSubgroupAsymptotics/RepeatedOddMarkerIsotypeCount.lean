import SymmetricSubgroupAsymptotics.RepeatedOddMarkerModelSum
import SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleWeights

/-!
# Original repeated-marker count as an exact product of isotype factors

The source B is the literal binary sign/exterior image. The submodule sum
is reindexed by the exact full-coordinate isotype equivalence. Scalar
labels distinguish exactly the original sign homomorphisms on this same B.
No canonical bases, physical relabellings, or normalizer factors are added.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerIsotypeCount

open RepeatedOddMarkerModelSum DiagonalInvariantSubmodules
open DiagonalFullSubmoduleEquiv DiagonalFullSubmoduleWeights

variable {ι D : Type} [Fintype ι] [Group D]
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))

abbrev actualScalar := TernaryDiagonalQuotientCocycles.scalar
  (RepeatedOddMarkerKernelChart.signCharacter B)

/-- Equality of these whole scalar labels is precisely equality of the
original sign homomorphisms on B, including all their correlations. -/
theorem actualScalar_eq_iff (i j : ι) :
    actualScalar B i = actualScalar B j ↔
      RepeatedOddMarkerKernelChart.signCharacter B i =
        RepeatedOddMarkerKernelChart.signCharacter B j :=
  OddMarkerTernaryChart.signScalar_characters_eq_iff _ _

/-- Flatten only the proof fields; the literal original submodule is
identical in both directions. -/
def admissibleEquivFullStable : AdmissibleKernel B ≃ FullStable (actualScalar B) where
  toFun K := ⟨⟨K.1, K.2.1⟩, K.2.2⟩
  invFun K := ⟨K.1.1, K.1.2, K.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

local instance admissibleFinite : Finite (AdmissibleKernel B) :=
  Finite.of_injective (fun K : AdmissibleKernel B => (K.1 : Set (ι → ZMod 3)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance fullStableFinite : Finite (FullStable (actualScalar B)) :=
  Finite.of_injective (fun K : FullStable (actualScalar B) =>
    (K.1.1 : Set (ι → ZMod 3)))
    (fun _ _ h => Subtype.ext (Subtype.ext (SetLike.coe_injective h)))

attribute [local instance] Fintype.ofFinite

/-- The complete original fixed-image count is one full-subspace factor
for each distinct actual sign and its entire original coordinate fibre. -/
theorem card_imageFull_product (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    Nat.card (ImageFull B) =
      ∏ a : Label (actualScalar B),
        ternaryFullWeight (Coordinate (actualScalar B) a) := by
  rw [RepeatedOddMarkerModelSum.card_imageFull B hB hχ]
  calc
    _ = ∑ K : FullStable (actualScalar B),
        (3 : ℕ) ^ (Fintype.card ι - Module.finrank (ZMod 3) K.1.1) :=
      Fintype.sum_equiv (admissibleEquivFullStable B) _ _ (fun _ => rfl)
    _ = _ := fullStable_weight_sum (actualScalar B)

theorem card_imageFull_product_rat (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    (Nat.card (ImageFull B) : ℚ) =
      ∏ a : Label (actualScalar B),
        (ternaryFullWeight (Coordinate (actualScalar B) a) : ℚ) := by
  exact_mod_cast card_imageFull_product B hB hχ

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerIsotypeCount

end
