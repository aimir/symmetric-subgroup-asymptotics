import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeRootIntersections
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.Ring

/-! Every abelian image of the actual fixed group is covered by the images
of its two positive simple inversion blocks. Their proved cardinalities are
q and q². This yields an all-parameter abelianization bound without asserting
perfectness or the exceptional parameter's customary derived index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourAbelianImageCardinality
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedAmbientHom CFSGReeFFourMinimalParabolics
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourSignedBlockGeneration CFSGReeFFourOriginalNegativeRootIntersections
open CFSGOpposedSubgroupPeeling

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

def positiveBlock (m : ℕ) (b : Bool) : Subgroup (originalModelFixed m) :=
  inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)

theorem positiveBlock_card (m : ℕ) (b : Bool) :
    Nat.card (positiveBlock m b) = (2^(2*m+1))^(if b then 2 else 1) :=
  simple_inversion_card m b

variable {A : Type*} [CommGroup A]

theorem range_eq_block_join (m : ℕ) (f : originalModelFixed m →* A) :
    f.range = (positiveBlock m false).map f ⊔ (positiveBlock m true).map f := by
  let S : Subgroup (originalModelFixed m) :=
    ((positiveBlock m false).map f ⊔ (positiveBlock m true).map f).comap f
  have hpos (b : Bool) : positiveBlock m b ≤ S := by
    intro x hx
    change f x ∈ (positiveBlock m false).map f ⊔ (positiveBlock m true).map f
    cases b
    · exact Subgroup.mem_sup_left ⟨x, hx, rfl⟩
    · exact Subgroup.mem_sup_right ⟨x, hx, rfl⟩
  have hneg (b : Bool) : fixedNegative m ⊓ simpleParabolic m b ≤ S := by
    intro x hx
    rw [negative_inf_simpleParabolic_eq_opposition_inversion] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    change f (oppositionFixed m * u * (oppositionFixed m)⁻¹) ∈
      (positiveBlock m false).map f ⊔ (positiveBlock m true).map f
    have he : f (oppositionFixed m * u * (oppositionFixed m)⁻¹) = f u := by
      rw [map_mul, map_mul, map_inv, mul_comm (f (oppositionFixed m)) (f u),
        mul_assoc, mul_inv_cancel, mul_one]
    rw [he]
    exact hpos b hu
  have htop : S = ⊤ := subgroup_eq_top_of_signed_blocks m S hpos hneg
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have hg : g ∈ S := by rw [htop]; trivial
    exact hg
  · apply sup_le <;> rintro _ ⟨g, _, rfl⟩ <;> exact ⟨g, rfl⟩

theorem exists_block_image_factors (m : ℕ) (f : originalModelFixed m →* A)
    (g : originalModelFixed m) :
    ∃ u : positiveBlock m false, ∃ v : positiveBlock m true, f g = f u.val * f v.val := by
  have hg : f g ∈ (positiveBlock m false).map f ⊔ (positiveBlock m true).map f := by
    rw [← range_eq_block_join]
    exact ⟨g, rfl⟩
  obtain ⟨x, hx, y, hy, he⟩ := Subgroup.mem_sup.mp hg
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨⟨u, hu⟩, ⟨v, hv⟩, he.symm⟩

theorem card_le_of_surjective (m : ℕ) (f : originalModelFixed m →* A)
    (hf : Function.Surjective f) : Nat.card A ≤ (2^(2*m+1))^3 := by
  let F : positiveBlock m false × positiveBlock m true → A :=
    fun p => f p.1.val * f p.2.val
  have hF : Function.Surjective F := by
    intro a
    obtain ⟨g, rfl⟩ := hf a
    obtain ⟨u, v, he⟩ := exists_block_image_factors m f g
    exact ⟨(u, v), he.symm⟩
  have hc := Nat.card_le_card_of_surjective F hF
  simp only [Nat.card_prod, positiveBlock_card, Bool.false_eq_true, if_false, if_true,
    pow_one] at hc
  calc
    Nat.card A ≤ 2^(2*m+1) * (2^(2*m+1))^2 := hc
    _ = (2^(2*m+1))^3 := by ring

theorem abelianization_card_le (m : ℕ) :
    Nat.card (Abelianization (originalModelFixed m)) ≤ (2^(2*m+1))^3 :=
  card_le_of_surjective m Abelianization.of
    (QuotientGroup.mk'_surjective (commutator (originalModelFixed m)))

end SymmetricSubgroupAsymptotics.CFSGReeFFourAbelianImageCardinality
