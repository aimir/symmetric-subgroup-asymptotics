import SymmetricSubgroupAsymptotics.TernaryDegreeNineClosure
import SymmetricSubgroupAsymptotics.TransitiveTernaryStabilityAwayFromTen

/-! The original literal degree9 inversion proof with the now-proved
stability bound installed only at its actual three-point top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The rank-two degree-nine endpoint fixes a literal three-by-three minimal
block system and a rank-one original normal top image. -/
theorem degreeNine_minimalBlock_data_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 3 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 := by
  letI : Nonempty Ω := ⟨ω₀⟩
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  let T := originalNormalRange D.topMap N
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 9 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hr3 : r = 3 := by
    have hrdiv : r ∣ 9 := ⟨s, hrs.symm⟩
    have hrle : r ≤ 9 := Nat.le_of_dvd (by decide) hrdiv
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  have hs3 : s = 3 := by
    have hrs' : 3 * s = 9 := by simpa only [hr3] using hrs
    omega
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
  let v := actualChiefSeriesTernaryWeight c
  have hv : v ≤ 1 := by
    have hv' : v ≤ r / 3 := by simpa only [v, r] using hc
    simpa only [hr3] using hv'
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  have ht : t ≤ 1 := by
    have ht' := transitiveTernaryHead_stability_without_catalogue_of_ne_ten
      hChief hgen hindex published8 h18 (A := D.Top) (X := D.Points)
      (by change s≠10; omega) T
    simpa only [t, s, hs3, ternaryStabilityBound_three] using ht'
  have hd := D.head_bound_nat N c
  have hd' : 2 ≤ v + t := by
    rw [hRank] at hd
    simpa only [s, hs3, ternaryIndexWidth_three, mul_one, v, t, T] using hd
  have htExact : t = 1 := by omega
  exact ⟨by simpa only [r] using hr3,
    by simpa only [s] using hs3,
    by simpa only [t, T] using htExact⟩

include D in
/-- Every degree-nine rank-two normal pair enters the existing transitive
3-group owner.  No finite action catalogue or group-order premise is used. -/
theorem degreeNine_rankTwo_isPGroup_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    IsPGroup 3 A := by
  obtain ⟨hFibre, hPoints, hTop⟩ := D.degreeNine_minimalBlock_data_without_catalogue
    hChief hgen hindex published8 h18 N hDegree hRank
  letI : Fintype D.Points := Fintype.ofFinite _
  letI (x : D.Points) : Fintype (originalBlockFibre D.map x) :=
    Fintype.ofFinite _
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTopGroup : IsPGroup 3 D.Top :=
    degreeThree_rankOne_isPGroup hPoints T (by simpa only [T] using hTop)
  let e := D.ternaryFibreCharts hFibre
  by_cases hSigns :
      DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant = 1
  · exact DegreeThreeBlockInversionHead.originalGroup_isPGroup_of_coordinateSigns_eq_one
      (hb := D.map_equivariant) D.map e hTopGroup hSigns
  · have hexists : ∃ x : D.Points,
        OriginalBlockSignCoordinates.coordinateSign D.map D.map_equivariant x ≠ 1 := by
      by_contra h
      simp only [not_exists, not_ne_iff] at h
      apply hSigns
      apply MonoidHom.ext
      intro k
      funext x
      simpa only [DegreeThreeBlockInversionHead.coordinateSigns,
        MonoidHom.one_apply] using DFunLike.congr_fun (h x) k
    obtain ⟨x₀, hx₀⟩ := hexists
    have hle :=
      DegreeThreeBlockInversionHead.originalNormal_primeRelativeHead_le_top
        (hb := D.map_equivariant) D.map N e x₀ hx₀
    rw [hRank, hTop] at hle
    omega

end OriginalMinimalBlock

/-- The minimal block is selected internally from an arbitrary original
degree-nine action. -/
theorem degreeNine_rankTwo_isPGroup_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    IsPGroup 3 A := by
  have hTwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hTwo
  have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
    intro hp
    letI : MulAction.IsPreprimitive A Ω := hp
    have hsafe := primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
      hgen hindex published8 A Ω (by omega) (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  exact D.degreeNine_rankTwo_isPGroup_without_catalogue
    hChief hgen hindex published8 h18 N hDegree hRank

end SymmetricSubgroupAsymptotics

end
