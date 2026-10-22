import SymmetricSubgroupAsymptotics.CFSGSufficientDegreeEighteenHead
import SymmetricSubgroupAsymptotics.CFSGSufficientSmallPrimitiveHeadsDirect
import SymmetricSubgroupAsymptotics.CFSGSufficientSmallExceptionalHeads
import SymmetricSubgroupAsymptotics.SmallTransitiveTernaryHeadWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeSixHighStructuralOwnerWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeSixHighStructuralOwnerCardWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeEighteenThreeBySixHeadWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeEighteenNineByTwoHeadWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeEighteenHeadFromActualSmallConsumers

/-! Direct actual-head forwarding; the ordinary primitive normal-generator input is absent.

 Complete degree18 head consumer from the sufficient hybrid. Every
original minimal block, top image, kernel intersection and original normal
is retained. The six/nine local bounds and the original three-by-six
coordinate proof are used, without a global strict-head premise. -/

/-! The direct actual degree6/9 small-head induction without degree18 or a
global strict-head input. Only actual local primitive6/9 bounds are used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- Every faithful transitive degree-six normal pair has ternary relative
head at most one. -/
theorem transitive_degreeSix_ternaryHead_le_one_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hdegree : Nat.card Ω = 6) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 1 := by
  have htwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    have h := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
       hindex published8 A Ω (by omega) (by omega) (by omega) (by omega) N
    omega
  · let ω₀ : Ω := Classical.choice inferInstance
    let D : OriginalMinimalBlock (A := A) ω₀ :=
      Classical.choice (originalMinimalBlock_nonempty ω₀ hp)
    let r := Nat.card D.Fibre
    let s := Nat.card D.Points
    have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
    have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
    have hrs : r * s = 6 := by
      simpa only [r, s, hdegree] using D.degree_product
    have hrle : r ≤ 6 := Nat.le_of_dvd (by decide) ⟨s, hrs.symm⟩
    have hsle : s ≤ 6 := Nat.le_of_dvd (by decide) ⟨r, by
      simpa [Nat.mul_comm] using hrs.symm⟩
    have hfactors : (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) := by
      interval_cases r <;> interval_cases s <;> omega
    letI : Nontrivial D.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
    letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
    letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
    letI : FaithfulSMul D.Top D.Points := D.top_faithful
    letI : Finite D.Top := D.top_finite
    let T := originalNormalRange D.topMap N
    rcases hfactors with h23 | h32
    · let c := actualChiefSeries D.Component
      have hc : actualChiefSeriesTernaryWeight c = 0 :=
        permutationChiefWeight_eq_zero_of_card_le_two D.Component c (by
          simpa only [r] using h23.1.le)
      have ht := transitive_degreeThree_ternaryHead_le_one T (by
        simpa only [s] using h23.2)
      have h := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 1 := by
        simpa only [T] using ht
      exact h.trans (by simpa only [hc, zero_mul, zero_add] using ht')
    · let c := actualChiefSeries D.Component
      have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
        permutationChiefWeight_le_one_of_card_le_five D.Component c (by
          simpa only [r] using h32.1.le.trans (by decide : 3 ≤ 5))
      have ht := transitive_degreeTwo_ternaryHead_eq_zero T (by
        simpa only [s] using h32.2)
      have h := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 0 := by
        simpa only [T] using ht
      have hsCard : Nat.card D.Points = 2 := by
        simpa only [s] using h32.2
      exact h.trans (by
        rw [ht', hsCard, ternaryIndexWidth_two, mul_one, add_zero]
        exact hc)

/-- Every faithful transitive degree-nine normal pair has ternary relative
head at most two, independently of the degree-eighteen theorem. -/
theorem transitive_degreeNine_ternaryHead_le_two_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hdegree : Nat.card Ω = 9) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 := by
  have htwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    have h := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
       hindex published8 A Ω (by omega) (by omega) (by omega) (by omega) N
    omega
  · let ω₀ : Ω := Classical.choice inferInstance
    let D : OriginalMinimalBlock (A := A) ω₀ :=
      Classical.choice (originalMinimalBlock_nonempty ω₀ hp)
    let r := Nat.card D.Fibre
    let s := Nat.card D.Points
    have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
    have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
    have hrs : r * s = 9 := by
      simpa only [r, s, hdegree] using D.degree_product
    have hrle : r ≤ 9 := Nat.le_of_dvd (by decide) ⟨s, hrs.symm⟩
    have hr3 : r = 3 := by
      interval_cases r <;> omega
    have hs3 : s = 3 := by
      rw [hr3] at hrs
      omega
    letI : Nontrivial D.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
    letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    let c := actualChiefSeries D.Component
    have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
      permutationChiefWeight_le_one_of_card_le_five D.Component c (by
        simpa only [r, hr3] using (by decide : 3 ≤ 5))
    letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
    letI : FaithfulSMul D.Top D.Points := D.top_faithful
    letI : Finite D.Top := D.top_finite
    let T := originalNormalRange D.topMap N
    have ht := transitive_degreeThree_ternaryHead_le_one T (by
      simpa only [s, hs3])
    have h := D.head_bound_nat N c
    have ht' : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 1 := by
      simpa only [T] using ht
    have hsCard : Nat.card D.Points = 3 := by
      simpa only [s] using hs3
    exact h.trans (by
      rw [hsCard, ternaryIndexWidth_three, mul_one]
      omega)

end SymmetricSubgroupAsymptotics

end


/-! The actual degree6 owner argument only needs its proved local primitive
strict bound, rather than a strict-head premise over every primitive action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Every high degree-six pair either already has the normal index-two
ternary owner, or its internally selected minimal block system is the sole
remaining two-by-three binary-block branch. -/
theorem degreeSix_high_oddIndexOwner_or_binaryBlock_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 6)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀),
        Nat.card D.Fibre = 2 ∧ Nat.card D.Points = 3 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
    intro hp
    letI : MulAction.IsPreprimitive A Ω := hp
    have hSafe := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
       hindex published8 A Ω (by omega) (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 6 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hfactors : (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) := by
    have hrdiv : r ∣ 6 := ⟨s, hrs.symm⟩
    have hrle : r ≤ 6 := Nat.le_of_dvd (by decide) hrdiv
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  rcases hfactors with hrs23 | hrs32
  · exact Or.inr ⟨ω₀, D, by simpa only [r] using hrs23.1,
      by simpa only [s] using hrs23.2⟩
  · exact Or.inl (D.degreeSix_ternaryBlock_owner N
      (by simpa only [r] using hrs32.1)
      (by simpa only [s] using hrs32.2) hHigh)

/-- Both intrinsic degree6 owners are retained on the same original group. -/
theorem degreeSix_high_structuralOwner_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hDegree : Nat.card Ω=6)
    (hHigh : 3*Nat.card Ω<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      Nonempty (C1CyclicBinaryModuleOwnerWitness A) := by
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock_of_sufficientHead
     hindex published8 N hDegree hHigh with hOdd|⟨x,D,hF,hP⟩
  · exact Or.inl hOdd
  · exact Or.inr (D.degreeSix_binaryBlock_owner N hF hP hHigh)

end SymmetricSubgroupAsymptotics

end


/-! The actual degree6 owner keeps its order-three complement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
theorem degreeSix_high_structuralOwnerWithComplementCard_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal] (hDegree : Nat.card X=6)
    (hHigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      ∃ W : C1CyclicBinaryModuleOwnerWitness A,Nat.card W.complement=3 := by
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock_of_sufficientHead
     hindex published8 N hDegree hHigh with hOdd|⟨x,D,hF,hP⟩
  · exact Or.inl hOdd
  · exact Or.inr (D.degreeSix_binaryBlock_ownerWithCard N hF hP hHigh)

end SymmetricSubgroupAsymptotics


/-! The actual3×6 degree18 proof with its two local six-point owner arguments
supplied by proved local bounds. No global strict-head input or degree18
stability is used. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock
variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [Finite A] [Finite Ω] [MulAction.IsPretransitive A Ω]
variable [FaithfulSMul A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- A degree-six top with relative head one supplies exactly the owner form
needed by the sharp abelian-kernel recurrence. -/
theorem degreeSix_top_cosetOwner_or_cyclic_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (T : Subgroup D.Top) [T.Normal]
    (hPoints : Nat.card D.Points = 6)
    (hT : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 1) :
    (∃ g : D.Top,
      MulAction.IsPretransitive (Subgroup.zpowers g)
        (D.Top ⧸ subgroupImage D.topMap.rangeRestrict
          (MulAction.stabilizer A D.base))) ∨
      (∃ W : C1CyclicBinaryModuleOwnerWitness D.Top,
        Nat.card W.complement = 3) := by
  letI : Finite D.Top := D.top_finite
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  have hHigh : 3 * Nat.card D.Points <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) := by
    rw [hPoints, hT]
    norm_num
  rcases degreeSix_high_structuralOwnerWithComplementCard_of_sufficientHead
       hindex published8 T hPoints hHigh with hOdd | ⟨W, hW⟩
  · left
    obtain ⟨W⟩ := hOdd
    have hTne : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 T) ≠ 0 := by omega
    obtain ⟨g, hg⟩ := W.exists_six_cycle_of_relativeHead_ne_zero
      hPoints T hTne
    refine ⟨g, ?_⟩
    letI : MulAction.IsPretransitive (Subgroup.zpowers g) D.Points := hg
    have hc : MulAction.IsPretransitive (Subgroup.zpowers g)
        (D.Top ⧸ MulAction.stabilizer D.Top D.base) :=
      cyclicQuotientStabilizer_pretransitive g D.base
    rw [D.topRange_stabilizer_image D.base]
    exact hc
  · exact Or.inr ⟨W, hW⟩

include D in
/-- In the all-even branch, the original intersection with the block kernel
has relative head at most one. -/
theorem threeBySix_allEven_kernelIntersection_head_le_one_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hPoints : Nat.card D.Points = 6)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (hSigns : DegreeThreeBlockInversionHead.coordinateSigns
      D.map D.map_equivariant = 1) :
    Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ D.topMap.ker)) ≤ 1 := by
  letI : Fintype D.Points := Fintype.ofFinite _
  let P : Subgroup A := N ⊓ D.topMap.ker
  letI : P.Normal := inferInstance
  let H : Subgroup A := MulAction.stabilizer A D.base
  let π : A →* D.Top := D.topMap.rangeRestrict
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  let c := actualChiefSeries D.Component
  have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
    permutationChiefWeight_le_one_of_card_le_five D.Component c (by
      rw [hFibre]
      norm_num)
  have hπker : π.ker = D.topMap.ker := MonoidHom.ker_rangeRestrict D.topMap
  letI : IsMulCommutative π.ker := by
    rw [hπker]
    exact DegreeThreeBlockInversionHead.kernel_isMulCommutative_of_coordinateSigns_eq_one
      (hb := D.map_equivariant) D.map (D.ternaryFibreCharts hFibre) hSigns
  have hP : P ≤ π.ker := by
    rw [hπker]
    exact inf_le_right
  have hKH : π.ker ≤ H := by
    exact D.topRange_kernel_le_stabilizer D.base
  let T := originalNormalRange D.topMap N
  letI : T.Normal := originalNormalRange_normal D.topMap N
  have hT : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 1 := by
    simpa only [T] using hTop
  have hOwner := D.degreeSix_top_cosetOwner_or_cyclic_of_sufficientHead  hindex published8 T hPoints hT
  have hSharp := actualLocalChiefHead_le_weight_of_owners
    π D.topMap.rangeRestrict_surjective P H hP hKH
    (originalBlockEvaluation D.map D.map_equivariant D.base P inf_le_right)
    (originalBlockProjection D.map D.map_equivariant D.base)
    (originalBlockEvaluation_conjugation D.map D.map_equivariant D.base P inf_le_right)
    (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    (originalBlockEvaluation_conjugates_separate
      D.map D.map_equivariant D.base P inf_le_right) c hOwner
  exact hSharp.trans hc

include D in
/-- Every normal pair in the three-by-six degree-eighteen orientation has
ternary relative head at most two. -/
theorem degreeEighteen_threeBySix_ternaryHead_le_two_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hPoints : Nat.card D.Points = 6) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 := by
  letI : Fintype D.Points := Fintype.ofFinite _
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite _
  let T := originalNormalRange D.topMap N
  letI : T.Normal := originalNormalRange_normal D.topMap N
  letI : Finite D.Top := D.top_finite
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  have hTopLe := transitive_degreeSix_ternaryHead_le_one_of_sufficientHead  hindex published8 T hPoints
  by_cases hTopZero : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 0
  · letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    let c := actualChiefSeries D.Component
    have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
      permutationChiefWeight_le_one_of_card_le_five D.Component c (by
        rw [hFibre]
        norm_num)
    have h := D.head_bound_nat N c
    rw [show Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 0 by
        simpa only [T] using hTopZero] at h
    rw [hPoints, ternaryIndexWidth_six, add_zero] at h
    omega
  · have hTopOne : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 T) = 1 := by omega
    let e := D.ternaryFibreCharts hFibre
    by_cases hSigns : DegreeThreeBlockInversionHead.coordinateSigns
        D.map D.map_equivariant = 1
    · have hKernel := D.threeBySix_allEven_kernelIntersection_head_le_one_of_sufficientHead
         hindex published8 N hFibre hPoints (by simpa only [T] using hTopOne) hSigns
      have hchain := primeRelativeHead_chain_le (N ⊓ D.topMap.ker) N 3 inf_le_left
      rw [primeRelativeHead_second_isomorphism 3 N D.topMap.ker,
        primeRelativeHead_original_range 3 D.topMap N] at hchain
      change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (N ⊓ D.topMap.ker)) +
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) at hchain
      omega
    · have hx : ∃ x : D.Points,
          OriginalBlockSignCoordinates.coordinateSign
            D.map D.map_equivariant x ≠ 1 := by
        by_contra h
        push_neg at h
        apply hSigns
        apply MonoidHom.ext
        intro k
        funext x
        have hx := congrArg (fun f :
          DegreeThreeBlockInversionHead.Kernel (A := A) (X := D.Points) →*
            Multiplicative (ZMod 2) => f k) (h x)
        simpa only [map_one] using hx
      obtain ⟨x, hx⟩ := hx
      have hInv := DegreeThreeBlockInversionHead.originalNormal_primeRelativeHead_le_top
        (hb := D.map_equivariant) D.map N e x hx
      change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) at hInv
      omega

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics

end


/-! The actual9×2 degree18 coordinate proof uses only the proved primitive9
relative-head bound. It does not use the degree18 stability theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock
variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [Finite A] [Finite Ω] [MulAction.IsPretransitive A Ω]
variable [FaithfulSMul A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

include D in
/-- Every normal pair in an actual nine-by-two minimal block system has
ternary relative head at most two. -/
theorem degreeEighteen_nineByTwo_ternaryHead_le_two_of_sufficientHead
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 9)
    (hPoints : Nat.card D.Points = 2) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 := by
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hFibre]; norm_num)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : Finite D.Top := D.top_finite
  let K := BlockKernelFullCoordinates.Kernel D.map D.map_equivariant D.base
  letI : K.Normal := inferInstance
  let eX : D.Points ≃ Fin 2 := Finite.equivFinOfCardEq hPoints
  let ρ : ∀ _ : Fin 2, K →* D.Component := fun i =>
    BlockKernelFullCoordinates.coordinate D.map D.map_equivariant D.base (eX.symm i)
  have hfree : ∀ (q : D.Top) (x : D.Points), q • x = x → q = 1 :=
    fun q x h => D.twoBlock_top_free hPoints q x h
  have honto : ∀ i, Function.Surjective (ρ i) := by
    intro i
    exact BlockKernelFullCoordinates.coordinate_surjective_of_free
      D.map D.map_equivariant D.base hfree (eX.symm i)
  have hfaithful : Function.Injective (fun k : K => fun i => ρ i k) := by
    intro k l hkl
    apply BlockKernelFullCoordinates.coordinates_injective
      D.map D.map_equivariant D.base
    funext x
    have h := congrFun hkl (eX x)
    simpa only [ρ, eX, Equiv.symm_apply_apply] using h
  have hcomponent : ∀ (_i : Fin 2) (M : Subgroup D.Component) (hM : M.Normal),
      letI := hM
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) ≤ 1 := by
    intro i M hM
    letI : M.Normal := hM
    have hstrict := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
       hindex published8 D.Component D.Fibre
      (by omega) (by omega) (by omega) (by omega) M
    rw [hFibre] at hstrict
    omega
  have hK : K = D.topMap.ker :=
    BlockKernelFullCoordinates.kernel_eq_topMap_ker
      D.map D.map_equivariant D.base
  let K₀ : Subgroup A := D.topMap.ker
  letI : K₀.Normal := inferInstance
  let eK : K₀ ≃* K := MulEquiv.subgroupCongr hK.symm
  let ρ₀ : ∀ _ : Fin 2, K₀ →* D.Component := fun i =>
    (ρ i).comp eK.toMonoidHom
  have honto₀ : ∀ i, Function.Surjective (ρ₀ i) := by
    intro i d
    obtain ⟨k, hk⟩ := honto i d
    obtain ⟨k₀, rfl⟩ := eK.surjective k
    exact ⟨k₀, hk⟩
  have hfaithful₀ : Function.Injective (fun k : K₀ => fun i => ρ₀ i k) := by
    intro k l hkl
    apply eK.injective
    apply hfaithful
    exact hkl
  let P₀ : Subgroup K₀ := N.subgroupOf K₀
  letI : P₀.Normal := subgroupOf_normal N K₀
  have hP₀ : Module.finrank (ZMod 3) (primeRelativeCharacters 3 P₀) ≤ 2 := by
    have h := primeRelativeHead_faithful_family_le 3 2
      (fun _ : Fin 2 => D.Component) ρ₀ honto₀ hfaithful₀
      (fun _ => 1) hcomponent P₀
    simpa using h
  have hIntersection₀ : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ K₀)) ≤ 2 :=
    (primeRelativeHead_inf_le_subgroupOf 3 N K₀).trans hP₀
  let T := originalNormalRange D.topMap N
  letI : T.Normal := originalNormalRange_normal D.topMap N
  have hTopCard : Nat.card D.Top = 2 := D.twoBlock_top_card hPoints
  have hTopPGroup : IsPGroup 2 D.Top :=
    IsPGroup.of_card (n := 1) (by simpa using hTopCard)
  have hTzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 T) = 0 :=
    primeRelativeHead_power_group 3 T 2 (by decide) (hTopPGroup.to_subgroup T)
  have hchain := primeRelativeHead_chain_le (N ⊓ K₀) N 3 inf_le_left
  rw [primeRelativeHead_second_isomorphism 3 N K₀] at hchain
  change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 (N ⊓ K₀)) +
        Module.finrank (ZMod 3)
          (primeRelativeCharacters 3
            (normalChainQuotient D.topMap.ker N)) at hchain
  rw [primeRelativeHead_original_range 3 D.topMap N, hTzero] at hchain
  exact hchain.trans (by simpa using hIntersection₀)

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics

end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem degreeEighteenTernaryHeadBound_of_actual_small_heads_of_sufficientHead
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification) :
    DegreeEighteenTernaryHeadBound := by
  intro A Ω _ _ _ _ _ _ _ hDegree N _
  have htwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    exact primitive_degreeEighteen_ternaryHead_le_two_of_sufficient
      hindex A Ω hDegree N
  · let ω₀ : Ω := Classical.choice inferInstance
    let D : OriginalMinimalBlock (A := A) ω₀ :=
      Classical.choice (originalMinimalBlock_nonempty ω₀ hp)
    let r := Nat.card D.Fibre
    let s := Nat.card D.Points
    have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
    have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
    have hrs : r * s = 18 := by
      simpa only [r, s, hDegree] using D.degree_product
    have hrle : r ≤ 18 := Nat.le_of_dvd (by decide) ⟨s, hrs.symm⟩
    have hsle : s ≤ 18 := Nat.le_of_dvd (by decide) ⟨r, by
      simpa [Nat.mul_comm] using hrs.symm⟩
    have hfactors :
        (r = 2 ∧ s = 9) ∨ (r = 3 ∧ s = 6) ∨
          (r = 6 ∧ s = 3) ∨ (r = 9 ∧ s = 2) := by
      interval_cases r <;> interval_cases s <;> omega
    letI : Nontrivial D.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
    letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
    letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
    letI : FaithfulSMul D.Top D.Points := D.top_faithful
    letI : Finite D.Top := D.top_finite
    let T := originalNormalRange D.topMap N
    rcases hfactors with h29 | h36 | h63 | h92
    · let c := actualChiefSeries D.Component
      have hc : actualChiefSeriesTernaryWeight c = 0 :=
        permutationChiefWeight_eq_zero_of_card_le_two D.Component c (by
          simpa only [r] using h29.1.le)
      have ht := transitive_degreeNine_ternaryHead_le_two_of_sufficientHead  hindex published8 T (by
        simpa only [s] using h29.2)
      have hd := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 2 := by
        simpa only [T] using ht
      exact hd.trans (by simpa only [hc, zero_mul, zero_add] using ht')
    · exact D.degreeEighteen_threeBySix_ternaryHead_le_two_of_sufficientHead
         hindex published8 N (by simpa only [r] using h36.1)
          (by simpa only [s] using h36.2)
    · obtain ⟨c, hc⟩ := primitiveDegreeSix_chiefWeight_zero_of_sufficient
        hindex D.Component D.Fibre (by simpa only [r] using h63.1)
      have ht := transitive_degreeThree_ternaryHead_le_one T (by
        simpa only [s] using h63.2)
      have hd := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 1 := by
        simpa only [T] using ht
      have hone := hd.trans (by simpa only [hc, zero_mul, zero_add] using ht')
      omega
    · exact D.degreeEighteen_nineByTwo_ternaryHead_le_two_of_sufficientHead
         hindex published8 N (by simpa only [r] using h92.1)
          (by simpa only [s] using h92.2)


end SymmetricSubgroupAsymptotics
