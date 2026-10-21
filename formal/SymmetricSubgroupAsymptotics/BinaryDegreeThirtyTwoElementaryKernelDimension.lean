import SymmetricSubgroupAsymptotics.BooleanFourTranslationHeadDimension
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineElementaryTop
import SymmetricSubgroupAsymptotics.BinaryPairRankTwoTopOrders

/-! A rank-nine original source with elementary sixteen-point top has
kernel dimension at most twelve. Four translations are recovered in the
actual top; the coefficient-prefix argument retains all lower terms and
does not assume that the kernel is a monomial ideal or that the outer
extension splits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_nine_elementary_kernel_finrank_le_twelve
    (hU : IsPGroup 2 U) (hhigh : 9 ≤ MarkedC4.genRank U)
    (hpow : ∀ t : F.top.range,t ^ 2 = 1) :
    Module.finrank (ZMod 2) F.kernelSpace ≤ 12 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  have hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16) :=
    BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
  have ht := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent
    hel (0 : Fin 16) 4 (by norm_num only [Nat.card_fin]) (⊤ : Subgroup F.top.range)
  have htgen := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
  have hgen : MarkedC4.genRank U ≤
      MarkedC4.normalGen F.top.ker + MarkedC4.genRank F.top.range := by
    letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
      rw [map_mul,map_mul,mul_comm])⟩⟩
    letI : IsMulCommutative F.top.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      infer_instance
    have hb := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
      F.top.rangeRestrict F.top.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict] at hb
    omega
  have hhead : 5 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) := by
    rw [representationHead_finrank_eq_coinvariants,←F.axisNatural_normalGen F.top.ker le_rfl hU]
    omega
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  obtain ⟨E,hzero,hH,hK⟩ := E₀.exists_original_elementary_zero_frame hTop hpow
  have hreg (j : Fin 3) : BinaryMenuCayley8T3.generators j ∈ E.top.range := by
    rw [hH]
    exact Subgroup.subset_closure ⟨j,rfl⟩
  have hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ E.kernelSpace := by
    rw [hK]
    simp only [BinaryCoordinateSpace.mem_iff]
    decide +kernel
  let e := E.commonBooleanPointLabels
  let u := E.commonTranslationRow hzero hreg hconst
  have htranslation (i : Fin 4) (x : Fin 16) :
      e ((u i)⁻¹ • e.symm x)=flipIndex i x := by
    have hh := E.commonTranslationRow_pointLabels hzero hreg hconst i
      ((u i)⁻¹ • e.symm x)
    change e ((u i) • ((u i)⁻¹ • e.symm x))=
      flipIndex i (e ((u i)⁻¹ • e.symm x)) at hh
    simp only [smul_inv_smul,Equiv.apply_symm_apply] at hh
    have he := congrArg (flipIndex i) hh
    simpa only [flipIndex_involutive i (e ((u i)⁻¹ • e.symm x))] using he.symm
  have hcomm (g : F.top.range) (i : Fin 4) : Commute g (u i) :=
    TransitiveTwoRegularOrbitChart.commutative_of_pow_two hpow g (u i)
  have hd := boolean_four_translation_head_five_dimension_le_twelve
    (F.axisNaturalSubrepresentation F.top.ker) e u htranslation hcomm hhead
  have haxis : (F.axisNaturalSubrepresentation F.top.ker).toSubmodule=F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a,rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  rwa [haxis] at hd

end SymmetricSubgroupAsymptotics.BinaryPairFrame
