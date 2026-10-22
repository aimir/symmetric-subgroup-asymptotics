import SymmetricSubgroupAsymptotics.CFSGSufficientTernarySmallOwners
import SymmetricSubgroupAsymptotics.CFSGSufficientTernaryStabilityDirect
import SymmetricSubgroupAsymptotics.CFSGSufficientDegreeEighteenHeadDirect
import SymmetricSubgroupAsymptotics.TernaryDegreeNineClosureWithoutCatalogue
import SymmetricSubgroupAsymptotics.TernaryDegreeTwentySevenReductionWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveBlockReductionWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveTopGeometryWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveStructuralOwnerWithoutCatalogue

/-! Direct actual-head forwarding; the ordinary primitive normal-generator input is absent.

 The original degree9/27 and imprimitive12 owner reductions from the
sufficient hybrid. Actual subgroups, minimal blocks, quotient images and
ternary relative heads are exactly those of the existing proof. -/

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
theorem degreeNine_minimalBlock_data_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
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
    have ht' := transitiveTernaryHead_stability_of_sufficientHead_of_ne_ten
      hChief  hindex published8 h18 (A := D.Top) (X := D.Points)
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
theorem degreeNine_rankTwo_isPGroup_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    IsPGroup 3 A := by
  obtain ⟨hFibre, hPoints, hTop⟩ := D.degreeNine_minimalBlock_data_of_sufficientHead
    hChief  hindex published8 h18 N hDegree hRank
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
theorem degreeNine_rankTwo_isPGroup_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
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
    have hsafe := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
       hindex published8 A Ω (by omega) (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  exact D.degreeNine_rankTwo_isPGroup_of_sufficientHead
    hChief  hindex published8 h18 N hDegree hRank

end SymmetricSubgroupAsymptotics

end


/-!
# Exact minimal-block data in the high degree-twenty-seven case

The numerical high-action recurrence orients the only two possible
factorizations of degree twenty seven.  The primitive fibre has degree three,
the faithful top has degree nine, and the original normal top image has exact
ternary relative rank two.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The high degree-twenty-seven recurrence fixes the literal minimal-block
orientation and the exact rank of the retained normal image in the top. -/
theorem highDegreeTwentySeven_minimalBlock_data_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 27)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 9 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 2 := by
  letI : Nonempty Ω := ⟨ω₀⟩
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  let T := originalNormalRange D.topMap N
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 27 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hrdiv : r ∣ 27 := ⟨s, hrs.symm⟩
  have hrle : r ≤ 27 := Nat.le_of_dvd (by decide) hrdiv
  have hrCases : r = 3 ∨ r = 9 := by
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
  let v := actualChiefSeriesTernaryWeight c
  have hv : v ≤ r / 3 := by simpa only [v, r] using hc
  have hd : d ≤ v * ternaryIndexWidth s + t := by
    simpa only [d, v, s, t, T] using D.head_bound_nat N c
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  have ht : t ≤ ternaryStabilityBound s := by
    simpa only [t, s, T] using
      (transitiveTernaryHead_stability_of_sufficientHead_of_ne_ten
        hChief  hindex published8 h18 (by
          change s≠10
          intro he
          rw [he] at hrs
          omega) T)
  have hdle : d ≤ 5 := by
    have h := transitiveTernaryHead_stability_of_sufficientHead_of_ne_ten
      hChief  hindex published8 h18 (A := A) (X := Ω) (by omega) N
    simpa only [d, hDegree, ternaryStabilityBound] using h
  have hHigh' : 81 < 20 * d := by
    simpa only [hDegree, d] using hHigh
  have hdExact : d = 5 := by omega
  rcases hrCases with hr3 | hr9
  · have hrs' : 3 * s = 27 := by simpa only [hr3] using hrs
    have hs9 : s = 9 := by omega
    have hv1 : v ≤ 1 := by simpa only [hr3] using hv
    have ht2 : t ≤ 2 := by
      simpa only [hs9, ternaryStabilityBound_nine] using ht
    have hd' : d ≤ 3 * v + t := by
      simpa only [hs9, ternaryIndexWidth_nine, Nat.mul_comm] using hd
    have htExact : t = 2 := by omega
    exact ⟨by simpa only [r] using hr3,
      by simpa only [s] using hs9,
      by simpa only [t, T] using htExact⟩
  · have hrs' : 9 * s = 27 := by simpa only [hr9] using hrs
    have hs3 : s = 3 := by omega
    have hv3 : v ≤ 3 := by simpa only [hr9] using hv
    have ht1 : t ≤ 1 := by
      simpa only [hs3, ternaryStabilityBound_three] using ht
    have hd' : d ≤ v + t := by
      simpa only [hs3, ternaryIndexWidth_three, mul_one] using hd
    omega

include D in
/-- The structural degree-nine closure puts the exact top pair in a 3-group;
therefore every high degree-twenty-seven pair on this literal minimal block
enters the same owner. -/
theorem highDegreeTwentySeven_isPGroup_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 27)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsPGroup 3 A := by
  obtain ⟨hFibre, hPoints, hTop⟩ :=
    highDegreeTwentySeven_minimalBlock_data_of_sufficientHead (D := D)
      hChief  hindex published8 h18 N hDegree hHigh
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTopGroup : IsPGroup 3 D.Top :=
    SymmetricSubgroupAsymptotics.degreeNine_rankTwo_isPGroup_of_sufficientHead
      hChief  hindex published8 h18 T hPoints (by
      simpa only [T] using hTop)
  apply D.degreeTwentySeven_high_isPGroup N hDegree hFibre hTopGroup
  · omega
  · exact hHigh

end OriginalMinimalBlock

/-- The degree-twenty-seven branch of the global high-action menu, with the
minimal block chosen internally from the original imprimitive action. -/
theorem highDegreeTwentySeven_imprimitive_isPGroup_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hDegree : Nat.card Ω = 27)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsPGroup 3 A := by
  have hTwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hTwo
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  exact OriginalMinimalBlock.highDegreeTwentySeven_isPGroup_of_sufficientHead (D := D)
    hChief  hindex published8 h18 N hDegree hHigh

end SymmetricSubgroupAsymptotics

end


/-!
# Structural reduction of the high degree-twelve branch

An actual minimal block system in degree twelve has factorization
`2 × 6`, `3 × 4`, `4 × 3`, or `6 × 2`.  For a normal pair above the
relative `3/20` line the first and last orientations are impossible.
Moreover, in either surviving orientation the minimal-block head recurrence
is sharp: the chosen primitive fibre chief series has ternary weight one,
the original normal top image has relative ternary rank one, and the original
normal subgroup has relative ternary rank two.

Thus the remaining degree-twelve ownership question is a structural problem
for the two natural geometries `3 × 4` and `4 × 3`; it no longer requires a
blind scan through all 301 transitive actions.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Every high degree-twelve normal pair has a minimal block system of type
`3 × 4` or `4 × 3`, and all three terms in the resulting head comparison
attain their forced values. -/
theorem degreeTwelve_high_imprimitive_minimalBlock_data_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀)
        (c : ActualChiefSeries D.Component),
      ((Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 4) ∨
        (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 3)) ∧
      actualChiefSeriesTernaryWeight c = 1 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 ∧
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 12 := by
    rw [D.degree_product, hDegree]
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
  let v := actualChiefSeriesTernaryWeight c
  have hv : v ≤ r / 3 := by simpa only [v, r] using hc
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  have hd : d ≤ v * ternaryIndexWidth s + t := by
    simpa only [d, v, s, t, T] using D.head_bound_nat N c
  have ht : t ≤ ternaryStabilityBound s := by
    simpa only [t, s, T] using
      (transitiveTernaryHead_stability_of_sufficientHead_of_ne_ten
        hChief  hindex published8 h18 (by
          change s≠10
          intro he
          rw [he] at hrs
          omega) T)
  have hdTwo : 2 ≤ d := by
    change 3 * Nat.card Ω < 20 * d at hHigh
    rw [hDegree] at hHigh
    omega
  have horient : (r = 3 ∧ s = 4) ∨ (r = 4 ∧ s = 3) := by
    have hfactors :
        (r = 2 ∧ s = 6) ∨ (r = 3 ∧ s = 4) ∨
          (r = 4 ∧ s = 3) ∨ (r = 6 ∧ s = 2) := by
      have hrle : r ≤ 6 := by nlinarith
      by_cases hr2 : r = 2
      · exact Or.inl ⟨hr2, by nlinarith⟩
      by_cases hr3 : r = 3
      · exact Or.inr (Or.inl ⟨hr3, by nlinarith⟩)
      by_cases hr4 : r = 4
      · exact Or.inr (Or.inr (Or.inl ⟨hr4, by nlinarith⟩))
      have hr5 : 5 ≤ r := by omega
      have hr6 : r = 6 := by
        by_cases h : r = 5
        · rw [h] at hrs
          omega
        · omega
      exact Or.inr (Or.inr (Or.inr ⟨hr6, by nlinarith⟩))
    rcases hfactors with h26 | h34 | h43 | h62
    · have hv0 : v = 0 := by
        apply permutationChiefWeight_eq_zero_of_card_le_two D.Component c
        change r ≤ 2
        omega
      have ht1 : t ≤ 1 := by
        have := ht
        norm_num [h26.2, ternaryStabilityBound] at this ⊢
        exact this
      have hd1 : d ≤ 1 := by
        rw [h26.2, hv0, zero_mul, zero_add] at hd
        exact hd.trans ht1
      omega
    · exact Or.inl h34
    · exact Or.inr h43
    · have hw := hWeight D.Component D.Fibre (by
            change 4 ≤ r
            omega)
          (by
            change r ≠ 9
            omega) c
      have hv1 : v ≤ 1 := by
        change 10 * v ≤ 3 * r at hw
        omega
      have ht0 : t = 0 := by
        have := ht
        simp only [h62.2, ternaryStabilityBound_two] at this
        omega
      have hd1 : d ≤ 1 := by
        have := hd.trans (Nat.add_le_add_right
          (Nat.mul_le_mul_right (ternaryIndexWidth s) hv1) t)
        simpa only [h62.2, ternaryIndexWidth_two, mul_one, ht0, add_zero] using this
      omega
  have hv1 : v ≤ 1 := by
    rcases horient with h34 | h43
    · simpa only [h34.1] using hv
    · simpa only [h43.1] using hv
  have ht1 : t ≤ 1 := by
    rcases horient with h34 | h43
    · simpa only [h34.2, ternaryStabilityBound_four] using ht
    · simpa only [h43.2, ternaryStabilityBound_three] using ht
  have hwidth : ternaryIndexWidth s = 1 := by
    rcases horient with h34 | h43
    · simp only [h34.2, ternaryIndexWidth_four]
    · simp only [h43.2, ternaryIndexWidth_three]
  have hdUpper : d ≤ 2 := by
    calc
      d ≤ v * ternaryIndexWidth s + t := hd
      _ ≤ 1 * 1 + 1 := Nat.add_le_add
        (Nat.mul_le_mul hv1 (le_of_eq hwidth)) ht1
      _ = 2 := by omega
  have hdEq : d = 2 := by omega
  have hvEq : v = 1 := by
    by_contra hvne
    have hv0 : v = 0 := by omega
    rw [hv0, zero_mul, zero_add] at hd
    omega
  have htEq : t = 1 := by
    by_contra htne
    have ht0 : t = 0 := by omega
    rw [hwidth, mul_one, ht0, add_zero, hdEq] at hd
    omega
  refine ⟨ω₀, D, c, ?_, ?_, ?_, ?_⟩
  · simpa only [r, s] using horient
  · simpa only [v] using hvEq
  · simpa only [t, T] using htEq
  · simpa only [d] using hdEq

end SymmetricSubgroupAsymptotics

end


/-! The original12-point top geometries on the actual imprimitive branch.
Primitive degree12 is deliberately retained for its semisimple owner. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- The full high degree-twelve reduction with the literal top action
identified in both surviving orientations. -/
theorem degreeTwelve_high_imprimitive_top_geometry_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀)
        (c : ActualChiefSeries D.Component),
      ((Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 4 ∧
          IsNaturalA4Action D.Top D.Points) ∨
        (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 3 ∧
          Nat.card D.Top = 3)) ∧
      actualChiefSeriesTernaryWeight c = 1 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 ∧
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2 := by
  obtain ⟨ω₀, D, c, horient, hv, ht, hd⟩ :=
    degreeTwelve_high_imprimitive_minimalBlock_data_of_sufficientHead
      hChief hWeight  hindex published8 h18 N himprimitive hDegree hHigh
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 T) = 1 := by
    simpa only [T] using ht
  refine ⟨ω₀, D, c, ?_, hv, ht, hd⟩
  rcases horient with h34 | h43
  · exact Or.inl ⟨h34.1, h34.2,
      degreeFour_rankOne_isNaturalA4 h34.2 T hTRank⟩
  · have hP : IsPGroup 3 D.Top :=
      degreeThree_rankOne_isPGroup h43.2 T hTRank
    exact Or.inr ⟨h43.1, h43.2,
      transitiveThreePoint_threePGroup_card h43.2 hP⟩

end SymmetricSubgroupAsymptotics

end


/-! The two original degree12 imprimitive geometries install the same owners;
primitive degree12 is kept for the new semisimple sector. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-- The two saturated degree-twelve orientations install their intrinsic
earlier owners, with the original normal subgroup and actual minimal block
system retained. -/
theorem degreeTwelve_high_imprimitive_structuralOwner_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsC1TernaryPrimeBaseOwner A ∨ IsC1BinaryNineTopOwner A Ω := by
  obtain ⟨ω₀, D, c, horient, hc, hTopRank, hRank⟩ :=
    degreeTwelve_high_imprimitive_top_geometry_of_sufficientHead
      hChief hWeight  hindex published8 h18 N himprimitive hDegree hHigh
  letI : Fintype D.Points := Fintype.ofFinite D.Points
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite (originalBlockFibre D.map x)
  rcases horient with h34 | h43
  · exact Or.inl
      (D.degreeTwelve_primeBase_owner N h34.1 h34.2.2 hRank hTopRank)
  · have hCard : ∀ x : D.Points,
        Nat.card (originalBlockFibre D.map x) = 4 := by
      intro x
      rw [D.originalBlockFibre_card_eq x, h43.1]
    let e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x :=
      fun x => (Finite.equivFinOfCardEq (hCard x)).symm
    exact Or.inr
      (D.fourByThree_nineTopOwner N c h43.2.1 h43.2.2 hc
        hTopRank hRank e)

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
