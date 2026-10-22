import SymmetricSubgroupAsymptotics.CFSGCompositionExtension
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! Actual-series composition bound from the full original nonaffine
socle and its actual outer-wreath embedding. No numerical simple-group
bound is assumed, and no quotient series is substituted for the input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNonaffineCoarseComposition
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem quotient_card_le_outer_wreath :
    Nat.card (G ⧸ finiteGroupSocle G) ≤
      Nat.card (Outer D.Simple) ^ D.factorCount * D.factorCount.factorial := by
  have h := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
  simpa only [OuterWreathPermutationCompression.Wreath, PermutationalWreathProduct.natCard_eq,
    Nat.card_fin, Nat.card_perm] using h

theorem composition_length_le_factors_add_quotient (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ D.factorCount + Real.logb 2 (Nat.card (G ⧸ finiteGroupSocle G)) := by
  let f := QuotientGroup.mk' (finiteGroupSocle G)
  let e : f.ker ≃* (Fin D.factorCount → D.Simple) :=
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (finiteGroupSocle G))).trans D.socleEquiv
  have h := CFSGCompositionExtension.length_le_kernel_factors_add_logb_image f
    (fun _ : Fin D.factorCount => D.Simple) (fun _ => D.noncommutative) e s
  simpa only [Fintype.card_fin] using h

theorem composition_length_le_outer_wreath (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ D.factorCount +
      D.factorCount * Real.logb 2 (Nat.card (Outer D.Simple)) +
      Real.logb 2 D.factorCount.factorial := by
  have hcard : (Nat.card (G ⧸ finiteGroupSocle G) : ℝ) ≤
      (Nat.card (Outer D.Simple) : ℝ) ^ D.factorCount * D.factorCount.factorial := by
    exact_mod_cast quotient_card_le_outer_wreath D
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := G ⧸ finiteGroupSocle G))) hcard
  have ho : (Nat.card (Outer D.Simple) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Outer D.Simple)).ne'
  have hf : (D.factorCount.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos D.factorCount).ne'
  rw [Real.logb_mul (pow_ne_zero _ ho) hf, Real.logb_pow] at hh
  linarith [composition_length_le_factors_add_quotient D s]

end SymmetricSubgroupAsymptotics.CFSGNonaffineCoarseComposition
