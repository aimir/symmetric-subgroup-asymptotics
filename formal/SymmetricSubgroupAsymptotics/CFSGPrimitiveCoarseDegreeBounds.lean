import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics
import SymmetricSubgroupAsymptotics.CFSGAffineCoarseComposition
import SymmetricSubgroupAsymptotics.CFSGNonaffineCoarseComposition
import SymmetricSubgroupAsymptotics.CFSGNonaffineNormalRank
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex
import SymmetricSubgroupAsymptotics.ActualWreathSemisimpleCoefficient

/-! Degree-only coarse primitive bounds from the two displayed simple-group
inputs. No primitive composition-length or primitive normal-generator
input is used. These are deliberately weaker than those sharp theorems. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveCoarseDegreeBounds
open PrimitiveSocleRawStructure CFSGCoarsePrimitiveNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem degree_parameters (hIndex : PublishedSimpleIndexBounds) (D : NonaffineData G X) :
    ∃ ell : ℕ, 5 ≤ ell ∧ ell ^ D.factorCount ≤ Nat.card X ∧
      (Nat.card (Outer D.Simple) : ℝ) ≤ 3 * Real.logb 2 ell := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have h5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨horder, hout⟩ := hIndex D.Simple D.noncommutative ell hell
  exact ⟨ell, h5, primitiveSocle_power_le_degree h5 horder (D.degreeForm hell), hout⟩

theorem nonaffine_composition_degree_bound (hIndex : PublishedSimpleIndexBounds)
    (D : NonaffineData G X) (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ (Real.logb 2 (Nat.card X))^2 + 3 * Real.logb 2 (Nat.card X) := by
  obtain ⟨ell, h5, hdegree, hout⟩ := degree_parameters hIndex D
  have h := socle_coarse_bound (c := 1) (by norm_num) h5
    (Nat.card_pos (α := Outer D.Simple)) hdegree hout
    (by simpa only [one_mul, add_assoc] using
      CFSGNonaffineCoarseComposition.composition_length_le_outer_wreath D s)
  norm_num at h ⊢
  exact h

private theorem quotient_logb_outer (D : NonaffineData G X) :
    Real.logb 2 (Nat.card (G ⧸ finiteGroupSocle G)) ≤
      D.factorCount * Real.logb 2 (Nat.card (Outer D.Simple)) + Real.logb 2 D.factorCount.factorial := by
  have hc : (Nat.card (G ⧸ finiteGroupSocle G) : ℝ) ≤
      (Nat.card (Outer D.Simple) : ℝ)^D.factorCount * D.factorCount.factorial := by
    exact_mod_cast CFSGNonaffineCoarseComposition.quotient_card_le_outer_wreath D
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := G ⧸ finiteGroupSocle G))) hc
  rw [Real.logb_mul (pow_ne_zero _ (by exact_mod_cast (Nat.card_pos (α := Outer D.Simple)).ne'))
    (by exact_mod_cast (Nat.factorial_pos D.factorCount).ne'), Real.logb_pow] at hh
  exact hh

theorem nonaffine_normal_rank_degree_bound (hIndex : PublishedSimpleIndexBounds)
    (D : NonaffineData G X) (hs : Group.rank D.Simple ≤ 2) (N : Subgroup G) [N.Normal] :
    (Group.rank N : ℝ) ≤ (Real.logb 2 (Nat.card X))^2 + 4 * Real.logb 2 (Nat.card X) := by
  obtain ⟨ell, h5, hdegree, hout⟩ := degree_parameters hIndex D
  have hN := CFSGNonaffineNormalRank.normal_rank_le_factors_add_quotient D hs N
  have hq := quotient_logb_outer D
  have h := socle_coarse_bound (c := 2) (by norm_num) h5
    (Nat.card_pos (α := Outer D.Simple)) hdegree hout (by linarith :
      (Group.rank N : ℝ) ≤ 2 * D.factorCount + D.factorCount * Real.logb 2 (Nat.card (Outer D.Simple)) +
        Real.logb 2 D.factorCount.factorial)
  norm_num at h ⊢
  exact h

theorem primitive_composition_degree_bound [FaithfulSMul G X] [Nontrivial X]
    [MulAction.IsPreprimitive G X] (hIndex : PublishedSimpleIndexBounds)
    (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ (Real.logb 2 (Nat.card X))^2 + 3 * Real.logb 2 (Nat.card X) := by
  classical
  obtain ⟨D⟩ := publishedONanScottStructure G X
  rcases D with D | P
  · exact nonaffine_composition_degree_bound hIndex D s
  · have hb := CFSGAffineCoarseComposition.composition_length_le_domain_log P (Classical.arbitrary X) s
    have hfloor := Real.natLog_le_logb (Nat.card X) 2
    change (Nat.log 2 (Nat.card X) : ℝ) ≤ Real.logb 2 (Nat.card X) at hfloor
    have hL : 0 ≤ Real.logb 2 (Nat.card X) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (Nat.card_pos (α := X)))
    have hm := mul_le_mul_of_nonneg_right hfloor hL
    nlinarith

theorem primitive_normal_rank_degree_bound [FaithfulSMul G X] [Nontrivial X]
    [MulAction.IsPreprimitive G X] (hIndex : PublishedSimpleIndexBounds)
    (hGen : FiniteSimpleTwoGeneratorBound) (N : Subgroup G) [N.Normal] :
    (Group.rank N : ℝ) ≤ (Real.logb 2 (Nat.card X))^2 + 4 * Real.logb 2 (Nat.card X) := by
  classical
  obtain ⟨D⟩ := publishedONanScottStructure G X
  rcases D with D | P
  · obtain ⟨A, hA, hc⟩ := hGen D.Simple inferInstance
      (centerless_of_nonabelian_simple D.Simple D.noncommutative)
    exact nonaffine_normal_rank_degree_bound hIndex D ((Group.rank_le hA).trans hc) N
  · have hb := CFSGAffineCoarseComposition.subgroup_rank_le_domain_log P (Classical.arbitrary X) N
    have hfloor := Real.natLog_le_logb (Nat.card X) 2
    change (Nat.log 2 (Nat.card X) : ℝ) ≤ Real.logb 2 (Nat.card X) at hfloor
    have hL : 0 ≤ Real.logb 2 (Nat.card X) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (Nat.card_pos (α := X)))
    have hm := mul_le_mul_of_nonneg_right hfloor hL
    nlinarith

end SymmetricSubgroupAsymptotics.CFSGPrimitiveCoarseDegreeBounds
