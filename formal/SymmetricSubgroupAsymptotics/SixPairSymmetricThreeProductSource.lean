import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3ProductAlgebra
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! The checked S3 × S3 normal-comparator algebra also supplies the SAME
abstract group at width12. Every original normal axis uses one of its two
actual S3 × C2 projections; the bottom axis uses its proved derived-cubic
tail. The original action is retained through the supplied group chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairSymmetricThreeProductSource
open Non2UnipotentPrefixFiniteMenu
variable (p : PreE7PairActionClass 6)
  (e : preE7PairAction 6 p ≃* DegreeSixS3Product.G)

def model : PreE7NormalComparatorModel 12 (preE7SixPairNonPairAction p) where
  G := DegreeSixS3Product.G
  equiv := e
  index := Bool
  R := DegreeSixS3Product.R
  degree := 5
  action := s3c2Action
  action_injective := s3c2Action_injective
  proj := DegreeSixS3Product.projection
  proj_surjective := DegreeSixS3Product.projection_surjective
  normal_cover := DegreeSixS3Product.algebra.normal_cover
  tailSlope := Real.logb 2 3/3
  tailConstant := Nat.card (DegreeSixS3Product.G ≃* DegreeSixS3Product.G)
  tailConstant_nonneg := by positivity
  tail := fun _ J => DegreeSixS3Product.algebra.target.epi_card_le_ternary J
  comparator_window := by norm_num [preE7CharacterRho,evenWidth,halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)

include p e in
private theorem normal_menu (b : ℕ) :
    (Nat.card ({N : Subgroup (preE7PairAction 6 p) // N.Normal}) : ℝ) ≤
      (2 : ℝ)^(16*(12 : ℝ)*Real.log ((12+b+2 : ℕ) : ℝ)^2) := by
  have h := (model p e).normalAxis_card_cast_le_modelRpow
  have hG : Nat.card (model p e).G=36 := DegreeSixS3Product.card_G
  rw [hG] at h
  apply h.trans
  apply le_trans _ (two_rpow_sixteen_width_le_menuMass (w := 12) (by norm_num) b)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) (by norm_num)

private theorem tail_menu (b : ℕ) :
    (model p e).tailConstant ≤
      (2 : ℝ)^(16*(12 : ℝ)*Real.log ((12+b+2 : ℕ) : ℝ)^2) := by
  have h : (model p e).tailConstant≤(2 : ℝ)^(216 : ℕ) := by
    change (Nat.card (DegreeSixS3Product.G ≃* DegreeSixS3Product.G) : ℝ) ≤ _
    exact_mod_cast DegreeSixS3Product.automorphism_card_le
  apply h.trans
  apply le_trans _ (two_rpow_thirtySix_width_le_menuMass (w := 12) (by norm_num) b)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) (by norm_num)

/-- Actual complete width12 source, not an earlier action substituted for it. -/
def source : PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  .inl (.ordinary .acert (.small ((model p e).numericalData .acert
    (normal_menu p e) (tail_menu p e))))

end SymmetricSubgroupAsymptotics.SixPairSymmetricThreeProductSource
