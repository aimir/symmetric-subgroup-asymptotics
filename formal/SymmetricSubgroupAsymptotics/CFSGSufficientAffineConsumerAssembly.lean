import SymmetricSubgroupAsymptotics.CFSGSufficientSixPointConsumers
import SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomyDirectSix
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6DirectSix
import SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6DirectSix
import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomialDirectSix
import SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSourceDirectSix
import SymmetricSubgroupAsymptotics.SixPairActualTopGeometryDirectSix
import SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSourceDirectSix
import SymmetricSubgroupAsymptotics.DegreeTwoSourceWithoutTwelveOrSixteenCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineActualConsumerAssembly

/-! The actual affine consumer uses the sufficient hybrid only through
its six-pair source. All original pair actions and EVERY normal denominator
in the B6 certificates remain literal. The proved twelve/sixteen actual
comparators, exceptional sources and all other affine inputs are unchanged.
No sharp universal simple-index theorem is reconstructed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomy.Sufficient
open OriginalKernelModuleChart

local instance primitiveSixDichotomy_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
  [act : MulAction B (Fin 6)] [faithful : FaithfulSMul B (Fin 6)]
  [primitive : MulAction.IsPreprimitive B (Fin 6)]
  (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
  (pi : G →* B) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) B) [Finite A] [FiniteDimensional (ZMod 2) A]
  (E : OriginalKernelModuleChart pi A)
  (hu : UniformSubrepresentationGeneratorBound A.ρ 1)

include hindex pi hpi A E hu act faithful primitive in
/-- Exhaustive alternatives on the unchanged quotient by the original N. -/
theorem quotientAlternative (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) 1 ∨
      (IsPGroup 2 (G ⧸ N) ∧ Nat.card (G ⧸ N) ≤ 8) := by
  let R := G ⧸ (pi.ker ⊔ N)
  let f : (G ⧸ N) →* R := base pi N
  let S : Rep.{0} (ZMod 2) R := E.sectionRepresentation pi A N
  letI : Finite S := by
    change Finite (E.sectionModule pi A N)
    exact Finite.of_surjective (E.sectionProjection pi A N)
      (E.sectionProjection_surjective pi A N)
  let C : OriginalKernelModuleChart f S := E.quotientChart pi A N
  have hf : Function.Surjective f := base_surjective pi N
  have hs : Function.Surjective (sectionTop pi N hpi) := by
    intro r
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) r
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  have hprops :
      (∀ L : Subgroup B,L.Normal → IsMulCommutative L → L=⊥) ∧
      (∀ L : Subgroup B,L.Normal → L≠⊥ → Nat.card (B⧸L)≤2) :=
    ⟨PrimitiveDegreeSixActualNormalConsumers.noAbelianNormal_of_sufficient hindex,
      PrimitiveDegreeSixActualNormalConsumers.normal_quotient_card_le_two_of_sufficient hindex⟩
  by_cases hN : N ≤ pi.ker
  · left
    have hi : Function.Injective (sectionTop pi N hpi) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply le_antisymm _ bot_le
      intro b hb
      obtain ⟨g,rfl⟩ := hpi b
      change sectionTop pi N hpi (pi g)=1 at hb
      have hz : QuotientGroup.mk' (pi.ker ⊔ N) g=1 :=
        (sectionTop_apply pi N hpi g).symm.trans hb
      have hg : g∈pi.ker ⊔ N := (QuotientGroup.eq_one_iff _).mp hz
      rw [sup_eq_left.mpr hN] at hg
      exact Subgroup.mem_bot.mpr hg
    let e : B ≃* R := MulEquiv.ofBijective (sectionTop pi N hpi) ⟨hi,hs⟩
    have hc : IsMulCommutative f.ker := IsMulCommutative.of_comm fun x y => by
      apply C.equiv.symm.injective
      rw [map_mul,map_mul,mul_comm]
    have huS : UniformSubrepresentationGeneratorBound S.ρ 1 := E.sectionUniform pi A N hpi hu
    have hkernel (L : Subgroup (G ⧸ N)) (hL : L.Normal) (hle : L ≤ f.ker) :
        MarkedC4.normalGen L ≤ 1 := by
      letI := hL
      exact C.kernel_normalGen_le f S hf 1 huS L hle
    have htopB (L : Subgroup B) (hL : L.Normal) : MarkedC4.normalGen L ≤ 1 := by
      letI := hL
      exact PrimitiveDegreeSixActualNormalConsumers.normalGen_le_one_of_sufficient hindex L
    have htop (L : Subgroup R) (hL : L.Normal) : MarkedC4.normalGen L ≤ 1 := by
      letI := hL
      exact CoprimeKernelQuotientSocles.normalGen_image_bound
        e.toMonoidHom e.surjective 1 htopB L
    exact PrimitiveSixSocleMapBridge.socle_le_max_of_map f hf hc 1 1 hkernel
      (PrimitiveSixSocleMapBridge.noAbelianNormal_of_equiv e.symm hprops.1) htop
  · right
    letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
    have hne : N.map pi≠⊥ := by
      intro hz
      exact hN ((Subgroup.map_eq_bot_iff (H := N)).mp hz)
    have hsmall : Nat.card R ≤ 2 :=
      (residualTop_card_eq pi hpi N).le.trans (hprops.2 (N.map pi) inferInstance hne)
    have hR : IsPGroup 2 R := by
      have hp : 0 < Nat.card R := Nat.card_pos
      by_cases hcard : Nat.card R=1
      · exact IsPGroup.of_card (n := 0) (by simpa using hcard)
      · have htwo : Nat.card R = 2 := by omega
        exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using htwo)
    have hk : IsPGroup 2 f.ker :=
      (ZModModule.isPGroup_multiplicative (n := 2) (G := S)).of_equiv C.equiv
    have hQ : IsPGroup 2 (G ⧸ N) := by
      have ht := (hR.to_subgroup (⊤ : Subgroup R)).comap_of_ker_isPGroup f hk
      have ht' : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := by
        simpa only [Subgroup.comap_top] using ht
      exact ht'.of_equiv Subgroup.topEquiv
    let idMap : Representation.IntertwiningMap A.ρ A.ρ :=
      { toLinearMap := LinearMap.id, isIntertwining' _ := rfl }
    have hgen : RepresentationGeneratedBy A.ρ 1 :=
      representationGeneratedBy_of_injective_of_uniform hu idMap (fun _ _ h => h)
    exact ⟨hQ,E.quotient_card_le_eight_of_cyclic_small_top pi hpi A N hgen hsmall⟩

include hindex pi hpi A E hu act faithful primitive in
/-- The historical B6 target alternatives, constructed before inspecting
any source group, with the original normal denominator unchanged. -/
def quotientCertificate (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : Subgroup G) [N.Normal] : PreE7B6QuotientCertificate (G ⧸ N) := by
  have h := quotientAlternative hindex pi hpi A E hu N
  by_cases hsoc : SocleNormalGeneratorBound (G ⧸ N) 1
  · let c := hZmud.generalCertificate hsoc
    apply PreE7B6QuotientCertificate.character c
    apply CharacterQuotientCertificate.slope_le_four_thirds_of_mixed c rfl rfl
    change 3 ^ 0 * 5 ^ 1 ≤ 15
    norm_num
  · have hb := h.resolve_left hsoc
    exact .binary hb.1 (hb.2.trans (by decide : 8 ≤ 32))


end SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomy.Sufficient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6.Sufficient
open Non2UnipotentPrefixFiniteMenu

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

private theorem kernel_uniform
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1) :
    UniformSubrepresentationGeneratorBound (kernelModule F).ρ 1 := by
  let j : Representation.IntertwiningMap (kernelModule F).ρ
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) :=
    { toLinearMap := F.kernelSpace.subtype, isIntertwining' _ := rfl }
  exact hu.of_injective j (fun _ _ h => Subtype.ext h)

/-- No finite normal menu or per-normal source bound is an input. -/
def actionCertificate [MulAction.IsPreprimitive F.top.range (Fin 6)]
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1) :
    PreE7B6ActionCertificate U where
  blockChart := sixPairBlockChart F
  preserves := sixPairBlockChart_preserves F
  quotient N := by
    letI := N.2
    letI : Finite (kernelModule F) := by
      change Finite F.kernelSpace
      infer_instance
    letI : FiniteDimensional (ZMod 2) (kernelModule F) := by
      change FiniteDimensional (ZMod 2) F.kernelSpace
      infer_instance
    exact PrimitiveSixOriginalQuotientDichotomy.Sufficient.quotientCertificate
      hindex F.top.rangeRestrict F.top.rangeRestrict_surjective (kernelModule F)
      (originalKernelChart F) (kernel_uniform F hu) hZmud N.1


end SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6.Sufficient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6.Sufficient
open BinarySixPointFiveCyclePolynomial Non2UnipotentPrefixFiniteMenu

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

def actionCertificate (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (a b : U) (q : Equiv.Perm (Fin 6))
    (ha : F.top a=SixPointFiveCyclePrimitive.cycle) (hb : F.top b=q)
    (hmoves : q 5≠5)
    (hmatrix : ∀ i x : Fin 6,
      actualOperator representation SixPointFiveCyclePrimitive.cycle q (Pi.single i 1) x=
        operator 0 (Pi.single i 1) x) : PreE7B6ActionCertificate U := by
  have haction (g : U) (p : Equiv.Perm (Fin 6)) (hg : F.top g=p) :
      permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)
        (F.top.rangeRestrict g)=representation p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((F.top g)⁻¹ x)=v (p⁻¹ x)
    rw [hg]
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1 :=
    uniform_of_actions 0 _ (F.top.rangeRestrict a) (F.top.rangeRestrict b)
      SixPointFiveCyclePrimitive.cycle q (haction a _ ha) (haction b _ hb) hmatrix
  letI : MulAction.IsPreprimitive F.top.range (Fin 6) :=
    SixPointFiveCyclePrimitive.preprimitive F.top.range
      (F.top.rangeRestrict a) (F.top.rangeRestrict b) ha
      (by change F.top b 5≠5; rwa [hb])
  exact SixPairPrimitiveAllNormalB6.Sufficient.actionCertificate F hindex hZmud hu


end SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6.Sufficient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial.Sufficient
open BinarySixPointFiveCyclePolynomial Non2UnipotentPrefixFiniteMenu

def actionCertificate
    {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds) (hZmud : ZmudFaithfulCharacterTupleInput)
    (a b : U) (ha : F.top a=SixPointFiveCyclePrimitive.cycle) (hb : F.top b 5≠5) :
    PreE7B6ActionCertificate U :=
  SixPairFiveCycleAllNormalB6.Sufficient.actionCertificate F hindex hZmud a b (F.top b) ha rfl hb
    (matrix (F.top b) hb)


end SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial.Sufficient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource.Sufficient
open Non2UnipotentPrefixFiniteMenu

variable (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
  (hZmud : ZmudFaithfulCharacterTupleInput)

/-- Only pair labels are changed; the original twelve-point group and
ALL literal normal denominators are retained. -/
def actionCertificate {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) [MulAction.IsPreprimitive F.top.range (Fin 6)] :
    PreE7B6ActionCertificate U := by
  apply Classical.choice
  obtain ⟨g,c,hc⟩ := PrimitiveSixActualCycleWitness.exists_original_point_conjugacy F.top.range
  obtain ⟨a,ha⟩ := F.top.rangeRestrict_surjective g
  let E := F.reindex c
  have he : E.top a=SixPointFiveCyclePrimitive.cycle := by
    have hag : F.top a=g.val := congrArg Subtype.val ha
    change c.permCongrHom (F.top a)=_
    rw [hag]
    exact hc
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq F.top.range (c.symm 5) (c.symm 0)
  obtain ⟨u,hu⟩ := F.top.rangeRestrict_surjective b
  have hmove : E.top u 5≠5 := by
    have hub : F.top u=b.val := congrArg Subtype.val hu
    change c (F.top u (c.symm 5))≠5
    rw [hub,show b.val (c.symm 5)=c.symm 0 from hb,c.apply_symm_apply]
    decide
  exact ⟨SixPairFiveCycleUniversalPolynomial.Sufficient.actionCertificate E hindex hZmud a u he hmove⟩

def source (p : PreE7PairActionClass 6)
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    [hprimitive : MulAction.IsPreprimitive F.top.range (Fin 6)] :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  .inl (.b6 (@actionCertificate hindex hZmud
    (preE7PairAction 6 p) F hprimitive))


end SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource.Sufficient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairActualTopGeometry.Sufficient
open Non2UnipotentPrefixFiniteMenu

def source_or_imprimitive
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds) (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6)
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)] :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) ⊕
      ImprimitiveGeometry F.top.range := by
  letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
  by_cases hp : MulAction.IsPreprimitive F.top.range (Fin 6)
  · letI := hp
    exact .inl (SixPairPrimitiveRepresentativeSource.Sufficient.source hindex hZmud p F)
  · exact .inr (imprimitiveGeometry F.top.range hp)


end SymmetricSubgroupAsymptotics.SixPairActualTopGeometry.Sufficient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource.Sufficient
open Non2UnipotentPrefixFiniteMenu

def source
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (p : PreE7PairActionClass 6) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  letI : MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12) :=
    preE7PairAction_pretransitive 6 p
  let F := preE7PairFrame 6 p
  cases SixPairActualTopGeometry.Sufficient.source_or_imprimitive hindex hZmud p F with
  | inl h => exact h
  | inr geometry =>
      letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
      apply SixPairActualNonbinaryTopSource.source p F _ hZmud lit
      intro M hM hnonbinary
      cases geometry with
      | threePairs E =>
          let B : BinaryPairFrame F.top.range (Fin 3) :=
            { frame := E.frame, top := E.top, intertwine := E.intertwine }
          exact SixPointThreePairNonbinaryQuotientSocles.quotient B M hnonbinary
      | twoTriples E =>
          exact SixPointTwoTripleNonbinaryQuotientSocles.quotient F.top.range E M hnonbinary

def representativeSource
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixPairRepresentativeSource := source hindex hZmud lit


end SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource.Sufficient

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.SufficientActualTwelve

/-- Keep the existing six-, eight- and sixteen-pair consumers; the entire
twelve-pair branch is supplied by the unconditional actual comparator. -/
def source_of_sixteenPairSource
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoGeneralSourceResidualAssembly.source_of_endpoints hZmud lit
    publishedThree (FourPairCanonicalClassification.classification hZmud published8)
    (SixPairActualCompleteRepresentativeSource.Sufficient.representativeSource hindex hZmud lit)
    (PairedEightActualRepresentativeSource.residualSource published8 hZmud lit)
    (degreeTwoTwelvePairResidualSource_of_representative actualTwelvePairRepresentativeSource)
    sixteenPair

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.SufficientActualTwelve
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu


/-! The degree-two source factory uses actual complete-moment comparators
at both counts12 and16. The finite pair catalogue datatypes and all older
stronger locator interfaces remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.SufficientActualTwelveSixteen

/-- No twelve- or sixteen-point classification is a parameter of the
actual binary-pair source factory. All retained inputs already occur inT1. -/
def source
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoClosedSourceAssembly.SufficientActualTwelve.source_of_sixteenPairSource
    hindex hZmud lit publishedThree published8
    (degreeTwoSixteenPairResidualSource_of_representative
      (actualSixteenPairRepresentativeSource hMN))

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.SufficientActualTwelveSixteen
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu


/-! Complete actual affine consumer assembly. The only finite primitive data
are the proved25/81/5 outputs. Degree8 uses proved actual facts, while every
degree16 branch stops at an actual elementary translation-kernel source.
The original finite catalogue APIs and their certificates remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
namespace ActualAffineSources

def consumerData_of_sufficient_actualFiniteData
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hcomp : PrimitiveCompositionLengthInput)
    (hKP : KovacsPraegerAbelianizationBound)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (D : ActualPrimitiveAffineFiniteData)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification) :
    PreE7PrimitiveAffineConsumerData := by
  let degreeTwo : PrimitiveAffineResidualDegreeSource 2 := DegreeTwoClosedSourceAssembly.SufficientActualTwelveSixteen.source
    hindex hZmud lit publishedThree published8 hMN
  let degreeThree : PrimitiveAffineResidualDegreeSource 3 := degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen publishedPairs
  let degreeFour : PrimitiveAffineResidualDegreeSource 4 := degreeFourActualResidualSource hZmud lit published8 hMN
    hClifford hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  let exceptional := PrimitiveAffineImprimitiveBlockTransfer.ActualAffineSources.preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources
      hZmud lit hgen hClifford hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm hSimpleGen degreeTwo degreeThree degreeFour
  let components := PrimitiveAffineImprimitiveBlockTransfer.ActualAffineSources.preE7PrimitiveAffineImprimitiveActualComponentSourceData hcomp hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm exceptional
  refine { primitive := ?_, imprimitive := ?_ }
  · intro w U hw hp P
    exact match D.primitiveSource hcomp hgen hKP U hw hp P with
      | .inl owner => .inl owner
      | .inr source => source
  · intro w U hw basePoint block P
    exact match components.source w U hw basePoint block P with
      | .inl source => imprimitiveAffineComponentTransfer hTraceyHalf hTraceyLog
          hTraceyRefined hTraceyPerm hSimpleGen block P source
      | .inr source => source

end ActualAffineSources
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
