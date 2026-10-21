import SymmetricSubgroupAsymptotics.BinaryPairAxisHeadFiveUniformSeven
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenElementaryZeroFrame
import SymmetricSubgroupAsymptotics.BinaryCommonEightOriginalTranslations
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

/-! The original rank-nine degree-thirty-two action with elementary
actual top has uniform natural-module width seven. The actual kernel
provides the five quadratic leading shears; no pure shear template is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

private theorem rank_nine_ordinary_rank_le_kernel_add_top :
    MarkedC4.genRank U ≤ MarkedC4.normalGen F.top.ker + MarkedC4.genRank F.top.range := by
  letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  letI : IsMulCommutative F.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hb := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    F.top.rangeRestrict F.top.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hb
  omega

private theorem rank_nine_constant_mem_regular23 : (fun _ : Fin 8 => (1 : ZMod 2)) ∈
    (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

theorem uniform_generatedBy_seven_of_rank_nine_elementary_top
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 9 ≤ MarkedC4.genRank U) (hpow : ∀ t : F.top.range, t ^ 2 = 1) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  have hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16) :=
    BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
  have ht := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent
    hel (0 : Fin 16) 4 (by norm_num only [Nat.card_fin] : Nat.card (Fin 16) = 2 ^ 4) (⊤ : Subgroup F.top.range)
  have htgen := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
  have hgen := F.rank_nine_ordinary_rank_le_kernel_add_top
  have hk : 5 ≤ MarkedC4.normalGen F.top.ker := by omega
  have hhead : 5 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) := by
    rw [representationHead_finrank_eq_coinvariants, ← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hk
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  obtain ⟨E, hzero, hH, hK⟩ := E₀.exists_original_elementary_zero_frame hTop hpow
  have hreg (j : Fin 3) : BinaryMenuCayley8T3.generators j ∈ E.top.range := by
    rw [hH]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ E.kernelSpace := by
    rw [hK]
    exact rank_nine_constant_mem_regular23
  let e := E.commonBooleanPointLabels
  apply F.uniform_generatedBy_seven_of_axis_head_five e _ hhead
  intro i
  let t := E.commonTranslationRow hzero hreg hconst i
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t
  have heq : F.top u = t.val := congrArg Subtype.val hu
  have hf (x : Fin 16) : e (F.top u x) = flipIndex i (e x) := by
    rw [heq]
    exact E.commonTranslationRow_pointLabels hzero hreg hconst i x
  refine ⟨u, ?_⟩
  intro j
  apply (F.top u).injective
  simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  apply e.injective
  rw [hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply, flipIndex_involutive]

end SymmetricSubgroupAsymptotics.BinaryPairFrame
