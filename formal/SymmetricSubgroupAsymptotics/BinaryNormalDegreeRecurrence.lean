import SymmetricSubgroupAsymptotics.BinaryPairKernelNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorActualIntersectionImage
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
import SymmetricSubgroupAsymptotics.BinaryExcessInductionNumerics
import SymmetricSubgroupAsymptotics.PermutationBinaryHead

/-! Unconditional normal-rank recurrences across original physical pair
frames. The image term is the actual original normal image, not a bound
on a replacement group or an auxiliary published generator assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I) [MulAction U I]
    (hact : ∀ (u : U) (i : I), u • i = F.top u i)

include hact

/-- Uniform generators on the original label module pay the actual
intersection term, leaving precisely the actual normal top image. -/
theorem normalGen_le_uniform_add_actual_top
    (H : ℕ) (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U I) H)
    (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ H + MarkedC4.normalGen (N.map F.top.rangeRestrict) := by
  have hk : F.top.rangeRestrict.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  apply normalGen_le_actual_intersection_add_image F.top.rangeRestrict
    F.top.rangeRestrict_surjective N H (MarkedC4.normalGen (N.map F.top.rangeRestrict)) _ le_rfl
  rw [hk]
  exact F.normalGen_le_of_uniform_pair_module hact H huniform
    (N ⊓ F.top.ker) inf_le_right

/-- A nonelementary original top costs a quarter of the original label
degree, plus the rank of the SAME actual normal top image. -/
theorem normalGen_le_quarter_add_actual_top
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := U) (X := I))
    (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ Nat.card I / 4 + MarkedC4.normalGen (N.map F.top.rangeRestrict) := by
  exact F.normalGen_le_uniform_add_actual_top hact _
    (twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary hU hnon) N

/-- An elementary original top of degree2^k costs at most its natural
middle width plus k, for every original normal subgroup. -/
theorem normalGen_le_middle_add_exponent_of_elementary_top
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := I))
    (i₀ : I) (k : ℕ) (hcard : Nat.card I = 2 ^ k)
    (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ k.choose (k / 2) + k := by
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range I := ⟨fun i j => by
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
    refine ⟨f u, ?_⟩
    change F.top u i = j
    rw [← hact]
    exact hu⟩
  have htopel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := I) := by
    intro a i
    obtain ⟨u, rfl⟩ := hf a
    change (f u) ^ 2 • i = i
    rw [← map_pow]
    change F.top (u ^ 2) i = i
    rw [← hact]
    exact hel u i
  have htop : MarkedC4.normalGen (N.map f) ≤ k :=
    ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent htopel i₀ k hcard (N.map f)
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U I) (k.choose (k / 2)) := by
    letI := Fintype.ofFinite I
    apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
    intro M
    exact twoGroup_permutationSubrepresentationHead_le_width hU k hcard i₀ M
  exact (F.normalGen_le_uniform_add_actual_top hact _ hu N).trans
    (Nat.add_le_add_left htop _)

/-- The elementary branch already fits the quarter physical-degree
budget once the original label exponent is at least5. -/
theorem normalGen_le_half_label_degree_of_elementary_top
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := I))
    (i₀ : I) (k : ℕ) (hk : 5 ≤ k) (hcard : Nat.card I = 2 ^ k)
    (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ Nat.card I / 2 := by
  have hb := (F.normalGen_le_middle_add_exponent_of_elementary_top hact hU hel i₀ k hcard N).trans
    (binary_middle_add_rank_le_half_power k hk)
  have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
    exact Nat.mul_comm _ _
  rw [hcard, hp, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact hb

end SymmetricSubgroupAsymptotics.BinaryPairFrame
