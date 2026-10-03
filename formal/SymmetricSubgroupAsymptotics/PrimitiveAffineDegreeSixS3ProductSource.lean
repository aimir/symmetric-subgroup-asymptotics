import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixNormalComparatorSource
import SymmetricSubgroupAsymptotics.OddMarker

/-!
# The degree-six `S₃ × S₃` affine cell

The zero-head degree-six classifier has one cell whose abstract group is
`S₃ × S₃`.  Its two sign projections have targets `S₃ × C₂`:

* `(x,y) ↦ (x, sign y)`, with kernel `1 × A₃`;
* `(x,y) ↦ (y, sign x)`, with kernel `A₃ × 1`.

Every nontrivial normal subgroup contains one of those kernels.  The bottom
axis is paid by one ternary cyclic dual on the full derived subgroup
`A₃ × A₃`.  This file keeps those two finite group facts together in
`Algebra`; the block-cell classifier only has to identify the literal ambient
group with the displayed product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Product

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev C2 := Multiplicative (ZMod 2)

/-- The exact target group. -/
abbrev G := S3 × S3

/-- The common degree-five comparator. -/
abbrev R := S3 × C2

/-- The full derived `A₃ × A₃`, expressed without replacing either
literal factor by an abstract cyclic group. -/
def derivedBase : Subgroup G :=
  ((oddMarkerSign.prodMap oddMarkerSign) : G →* C2 × C2).ker

/-- Forget the second alternating coordinate. -/
def leftProjection : G →* R :=
  (MonoidHom.id S3).prodMap oddMarkerSign

/-- Forget the first alternating coordinate. -/
def rightProjection : G →* R where
  toFun x := (x.2, oddMarkerSign x.1)
  map_one' := by simp
  map_mul' x y := by ext <;> simp

/-- The two quotient routes. -/
def projection : Bool → G →* R
  | false => leftProjection
  | true => rightProjection

theorem projection_surjective (j : Bool) : Function.Surjective (projection j) := by
  cases j <;> rintro ⟨s, c⟩
  · obtain ⟨t, ht⟩ := oddMarkerSign_surjective c
    exact ⟨(s, t), by simp [projection, leftProjection, ht]⟩
  · obtain ⟨t, ht⟩ := oddMarkerSign_surjective c
    exact ⟨(t, s), by simp [projection, rightProjection, ht]⟩

/-- The two finite group facts needed by the normal-comparator template.
They are separated from action recognition so a finite classifier cannot
silently substitute another degree-six permutation representation. -/
structure Algebra : Type where
  target : DerivedHead.DerivedCyclicTarget G derivedBase 0 3
  normal_cover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ →
    ∃ j : Bool, (projection j).ker ≤ N

theorem card_G : Nat.card G = 36 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]
  norm_num

theorem automorphism_card_le : Nat.card (G ≃* G) ≤ 2 ^ 216 := by
  calc
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) :=
      Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log G
    _ = 36 ^ 5 := by rw [card_G]; norm_num
    _ ≤ 2 ^ 216 := by norm_num

end DegreeSixS3Product

namespace Non2UnipotentPrefixFiniteMenu

/-- Recognition data for the literal retained action.  The finite
classification theorem is expected to construct only this equivalence. -/
structure PreE7DegreeSixS3ProductSource
    (U : PreE7NonPairActionClass 6) : Type where
  equiv : preE7NonPairAction 6 U ≃* DegreeSixS3Product.G

namespace PreE7DegreeSixS3ProductSource

variable {U : PreE7NonPairActionClass 6}
  (S : PreE7DegreeSixS3ProductSource U)
  (A : DegreeSixS3Product.Algebra)

/-- The exact normal-comparator model: two projections to the faithful
degree-five `S₃ × C₂` action and one ternary bottom tail. -/
def model : PreE7NormalComparatorModel 6 U where
  G := DegreeSixS3Product.G
  equiv := S.equiv
  index := Bool
  R := DegreeSixS3Product.R
  degree := 5
  action := s3c2Action
  action_injective := s3c2Action_injective
  proj := DegreeSixS3Product.projection
  proj_surjective := DegreeSixS3Product.projection_surjective
  normal_cover := A.normal_cover
  tailSlope := Real.logb 2 3 / 3
  tailConstant := Nat.card
    (DegreeSixS3Product.G ≃* DegreeSixS3Product.G)
  tailConstant_nonneg := by positivity
  tail := fun _ J => A.target.epi_card_le_ternary J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)

private theorem tailConstant_le :
    (S.model A).tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ)) := by
  change (Nat.card (DegreeSixS3Product.G ≃* DegreeSixS3Product.G) : ℝ) ≤ _
  calc
    (Nat.card (DegreeSixS3Product.G ≃* DegreeSixS3Product.G) : ℝ) ≤
        ((2 ^ 216 : ℕ) : ℝ) := by
      exact_mod_cast DegreeSixS3Product.automorphism_card_le
    _ = (2 : ℝ) ^ (36 * (6 : ℝ)) := by norm_num

/-- Completed degree-six source, ready for the exceptional-cell dispatcher
once the literal action has been classified as `S₃ × S₃`. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  DegreeSixNormalComparatorSource.source (S.model A) (S.tailConstant_le A)

end PreE7DegreeSixS3ProductSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
