import SymmetricSubgroupAsymptotics.RepeatedOddMarkerIsotypeCount

/-!
# Sum exact repeated-marker fibres over the original contraction images

The complete original model family is partitioned by its actual image.
The predicate is imposed on that same image and can retain all exterior
coordinate constraints. This is a model cardinality identity: no physical
normalizer divisor is applied to an individual image fibre.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerImageSum

open RepeatedOddMarkerKernel RepeatedOddMarkerModelSum
open RepeatedOddMarkerIsotypeCount DiagonalInvariantSubmodules DiagonalFullSubmoduleWeights

variable {ι D : Type} [Fintype ι] [Group D]

def Family (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :=
  {H : Subgroup ((ι → OddMarkerGroup) × D) //
    (∀ i, H.map (coordinate i)=⊤) ∧ P (H.map contraction)}

def ImageState (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :=
  {B : Subgroup ((ι → Multiplicative (ZMod 2)) × D) //
    (∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) ∧ P B}

def sigmaEquiv (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    Family P ≃ (Σ B : ImageState P, ImageFull B.1) where
  toFun H := ⟨⟨H.1.map contraction,by
      intro i hi
      obtain ⟨b,hb⟩ := RepeatedOddMarkerImage.signCharacter_nontrivial H.1 i (H.2.1 i)
      exact hb (DFunLike.congr_fun hi b),H.2.2⟩,⟨H.1,rfl,H.2.1⟩⟩
  invFun H := ⟨H.2.1,H.2.2.2,by
    rw [H.2.2.1]
    exact H.1.2.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨B,hχ,hP⟩,⟨H,hB,hfull⟩⟩
    cases hB
    rfl

/-- A binary exterior makes every literal sign/exterior subgroup binary.
The coordinate index is finite here for the count, although this power
argument itself uses a uniform exponent two on all signs. -/
theorem image_isPGroup (hD : IsPGroup 2 D)
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) : IsPGroup 2 B := by
  intro b
  obtain ⟨k,hk⟩ := hD b.1.2
  refine ⟨k+1,Subtype.ext ?_⟩
  apply Prod.ext
  · funext i
    change (b.1.1 i)^(2^(k+1))=1
    rw [pow_succ,Nat.mul_comm (2^k) 2,pow_mul,binary_mul_pow_two,one_pow]
  · change b.1.2^(2^(k+1))=1
    rw [pow_succ,pow_mul,hk,one_pow]

/-- The complete exterior projection is determined by the image, so
conditions on its individual original orbits can be retained in P. -/
theorem exterior_projection (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    (H.map contraction).map (MonoidHom.snd _ D)=H.map (MonoidHom.snd _ D) := by
  rw [Subgroup.map_map]
  rfl

section Finite

variable [Finite D]
local instance imageStateFinite
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    Finite (ImageState P) :=
  Finite.of_injective (fun B : ImageState P => B.1) Subtype.val_injective

local instance imageStateFintype
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    Fintype (ImageState P) := Fintype.ofFinite _

theorem card_family_fibres
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    Nat.card (Family P) = ∑ B : ImageState P, Nat.card (ImageFull B.1) := by
  calc
    Nat.card (Family P) = Nat.card (Σ B : ImageState P, ImageFull B.1) :=
      Nat.card_congr (sigmaEquiv P)
    _ = ∑ B : ImageState P, Nat.card (ImageFull B.1) := Nat.card_sigma

/-- Sum the whole model family before any physical relabelling or
normalizer division. The group in each summand is the actual original B. -/
theorem card_family (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    Nat.card (Family P) =
      ∑ B : ImageState P, ∏ a : Label (actualScalar B.1),
        ternaryFullWeight (Coordinate (actualScalar B.1) a) := by
  calc
    Nat.card (Family P) = ∑ B : ImageState P, Nat.card (ImageFull B.1) :=
      card_family_fibres P
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B _
      exact card_imageFull_product B.1 (image_isPGroup hD B.1) B.2.1

theorem card_family_rat (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    (Nat.card (Family P) : ℚ) =
      ∑ B : ImageState P, ∏ a : Label (actualScalar B.1),
        (ternaryFullWeight (Coordinate (actualScalar B.1) a) : ℚ) := by
  exact_mod_cast card_family hD P

/-- Named whole-family weight for consumers with dependent physical point
types. Its finite index is exactly the original image-state index above. -/
def familyWeight
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) : ℚ :=
  ∑ B : ImageState P, ∏ a : Label (actualScalar B.1),
    (ternaryFullWeight (Coordinate (actualScalar B.1) a) : ℚ)

theorem card_family_weight_rat (hD : IsPGroup 2 D)
    (P : Subgroup ((ι → Multiplicative (ZMod 2)) × D) → Prop) :
    (Nat.card (Family P) : ℚ) = familyWeight P :=
  card_family_rat hD P

end Finite

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerImageSum

end
