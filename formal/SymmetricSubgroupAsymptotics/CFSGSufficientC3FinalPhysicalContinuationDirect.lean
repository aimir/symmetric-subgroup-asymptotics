import SymmetricSubgroupAsymptotics.CFSGSufficientC3FinalPhysicalContinuation
import SymmetricSubgroupAsymptotics.CFSGSufficientC3AlignedOwnersDirect
import SymmetricSubgroupAsymptotics.CFSGSufficientC3PacketContinuationDirect
import SymmetricSubgroupAsymptotics.C3HighSemisimplePhysicalCover
import SymmetricSubgroupAsymptotics.C3ActualResidualClosure
import SymmetricSubgroupAsymptotics.C3ActualResidualForwardEstimate
import SymmetricSubgroupAsymptotics.C3HighSemisimpleForwardEstimate
import SymmetricSubgroupAsymptotics.C3CompleteActualPhysicalContinuation

/-! Direct actual-head forwarding; the ordinary primitive normal-generator input is absent.

 The complete original physical C3 continuation from sufficient-index
consumers. ONLY the hSI-dependent proofs are generalized here. The original
residual predicate, high-owner predicate, finite action index, three-sector
cover, ratio, numerical parameters and ALL normal/complement families are
the existing shared definitions. No high-owner estimate is a new premise. -/

/-! A separate high-C3 sector keeps the actual degree10/12 nonaffine orbit.
The outer regular C3 stays in the untouched complement. The cover uses the
finite set of literal actions, each carrying a proved actual-kernel rounding
datum; no finite classification or canonical action recognition is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- The actual high semisimple orbit on a complete original physical group. -/
theorem c3TrivialHigh_enters_structural_or_semisimple_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b n : ℕ) (e : TernaryCyclic⊕Fin b≃Fin n)
    (P : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    C3PhysicalStructuralOwner n (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) ∨
      C3PhysicalHighSemisimpleOwner n
        (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
  obtain ⟨o,N,hN,hHigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit := orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  rcases ternaryHigh_earlierOwner_or_semisimple_of_sufficientHead
    hChief hWeight  hindex published8 h18 N hHigh with hOld|hNew
  · exact Or.inl ⟨b,e,H,rfl,hH.1.1,o,N,hN,hHigh,hOld⟩
  · exact Or.inr ⟨b,e,H,rfl,hH.1.1,o,N,hN,hHigh,hNew⟩


theorem c3PhysicalHighSemisimpleOwner_finiteFusionCover_of_sufficientHead
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : C3PhysicalHighSemisimpleOwner n G) :
    ∃ j : C3HighSemisimpleIndex,∃ hn : c3SemisimpleHighWidth j.1≤n,
      G∈FusionWidthCanonicalFamily (c3HighSemisimpleAction j) hn (fun _ => True) := by
  rcases hG with ⟨b,e,H,hphysical,hfull,o,N,hN,hHigh,hOwner⟩
  have hdegree : b+3=n := by
    have hcard := Nat.card_congr e
    have hc : Nat.card TernaryCyclic=3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,Nat.card_fin]
    rw [Nat.card_sum,hc,Nat.card_fin,Nat.card_fin] at hcard
    omega
  subst n
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  let C : C3HighNestedCarrier.Data H := ⟨o,N,hN,hHigh⟩
  obtain ⟨d,hd⟩ : ∃ d : Fin 2,c3SemisimpleHighWidth d=Nat.card o.orbit := by
    rcases hOwner.2.1 with h10|h12
    · exact ⟨0,by simpa only [c3SemisimpleHighWidth,if_pos rfl] using h10.symm⟩
    · exact ⟨1,by simpa only [c3SemisimpleHighWidth,if_neg (by decide : (1 : Fin 2)≠0)] using h12.symm⟩
  let lab : o.orbit≃Fin (c3SemisimpleHighWidth d) := Finite.equivFinOfCardEq hd.symm
  let U := relabelSubgroup lab A
  let a : A≃*U := lab.permCongrHom.subgroupMap A
  let comp : LocalSemisimpleRoundingCompressionData U (c3SemisimpleHighWidth d) := by
    have cc := (hOwner.compression_of_sufficientHead hindex published8).comapEquiv a.symm
    exact cc.changeWidth hd.symm
  let j : C3HighSemisimpleIndex := ⟨d,U,⟨comp⟩⟩
  have hwidth : Nat.card C.orbit.orbit=c3SemisimpleHighWidth d := hd.symm
  have hn : c3SemisimpleHighWidth d≤b+3 := by
    have hh := C3HighNestedCarrier.width_le H o hd.symm
    omega
  refine ⟨j,hn,?_⟩
  rw [←hphysical]
  exact C3HighNestedCarrier.mem_widthCanonicalFamily_of_relabel H C hwidth U lab.symm
    (relabelSubgroup_symm lab A) e (fun _ => True) trivial


end SymmetricSubgroupAsymptotics


/-! After both old structural owners and the new actual semisimple owner
are removed on the complete physical subgroup, the high term is empty.
The same direct and low original-complement rows therefore remain. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem not_c3TrivialHigh_actualFinalResidual_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) (b : ℕ)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b))) :
    ¬C3TrivialHighPredicate b (C3ActualFinalResidualPredicate b) H := by
  intro hHigh
  have hr : C3ActualFinalResidualPredicate b H := hHigh.1.2
  have hRejects := (firstOwned_ownerOrResidual_last_iff
    c3PhysicalStructuralBranchMenu _).mp hr.1.2
  rcases c3TrivialHigh_enters_structural_or_semisimple_of_sufficientHead
    hChief hWeight  hindex published8 h18 b (3+b) (c3ResidualPointEquiv b)
    (C3ActualFinalResidualPredicate b) H hHigh with hOld|hNew
  · obtain ⟨i,hi⟩ := c3PhysicalStructuralBranchMenu_cover_of_sufficientHead
      hChief hWeight  hindex published8 h18 hOld
    exact hRejects i hi
  · exact hr.2 hNew


theorem c3ActualFinalResidual_highFamily_eq_empty_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) (b : ℕ) :
    FusionOrbitFamily ternaryRegularAction
      (C3TrivialHighPredicate b (C3ActualFinalResidualPredicate b))=∅ := by
  ext K
  constructor
  · intro hK
    obtain ⟨⟨e,⟨M,hM⟩⟩,rfl⟩ := hK
    obtain ⟨H,hHigh,rfl⟩ := hM
    exact False.elim (not_c3TrivialHigh_actualFinalResidual_of_sufficientHead
      hChief hWeight  hindex published8 h18 b H.1 H.2)
  · intro hK
    exact False.elim hK


theorem c3ActualFinalResidual_physical_frontier_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) (b : ℕ) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3ActualFinalResidualPredicate b))) : ℝ)/exactBenchmark (b+3)≤
    (c3DirectAxisKernel b+c3TrivialLowKernel b)*
      ((subgroupCount b : ℝ)/exactBenchmark b) := by
  have hh := c3Accepted_physical_frontier b (C3ActualFinalResidualPredicate b)
    (c3ActualFinalResidualPredicate_natural b)
  have hz : c3TrivialHighRatio b (C3ActualFinalResidualPredicate b)=0 := by
    unfold c3TrivialHighRatio
    rw [c3ActualFinalResidual_highFamily_eq_empty_of_sufficientHead
      hChief hWeight  hindex published8 h18 b]
    simp
  rw [hz] at hh
  simpa only [add_zero] using hh


end SymmetricSubgroupAsymptotics


/-! The exact existing residual kernel closes after excluding both owner
sectors. Its deleted degree and original complement stay unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open Filter
open scoped BigOperators

/-- Ambient-degree form of the complete final residual C3 family. -/
theorem c3ActualFinalResidualRatio_le_forwardRow_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 3 ≤ n) :
    c3ActualFinalResidualRatio n ≤
      ∑ b ∈ Finset.range n,
        c3FinalResidualForwardKernel n b * ordinarySubgroupRatio b := by
  have hadd : n - 3 + 3 = n := by omega
  have hlocal := c3ActualFinalResidual_physical_frontier_of_sufficientHead
    hChief hWeight  hindex published8 h18 (n-3)
  have hrow := fusionForwardRow_weighted_sum
    (fun _ : Unit => 3) (fun _ => c3FinalResidualKernelFactor)
    (fun _ => by norm_num) ordinarySubgroupRatio n (fun _ => hn)
  unfold c3ActualFinalResidualRatio
  rw [if_pos hn]
  rw [hadd] at hlocal
  have hrow' : (∑ b ∈ Finset.range n,
      c3FinalResidualForwardKernel n b * ordinarySubgroupRatio b) =
        c3FinalResidualKernelFactor (n-3) *
          ordinarySubgroupRatio (n-3) := by
    simpa only [c3FinalResidualForwardKernel, Fintype.sum_unique] using hrow
  exact hlocal.trans_eq hrow'.symm

/-- The c=1 residual sector is now a complete exponentially contractive
forward estimate, with no surviving high scalar term. -/

noncomputable def c3ActualFinalResidual_exponentialForwardEstimate_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3ActualFinalResidualRatio := by
  let W := c3FinalResidualForwardKernel_decay
  let C : ℝ := Classical.choose W
  have hCκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hCκ
  have hdecaySpec := Classical.choose_spec hCκ
  have hC : 0 < C := hdecaySpec.1
  have hκ : 0 < κ := hdecaySpec.2.1
  have hdecay := hdecaySpec.2.2
  let V := eventually_atTop.mp hdecay
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := c3FinalResidualForwardKernel
      threshold := max 3 N
      rate := κ
      scalarConst := 1
      rowConst := C
      rate_pos := hκ
      scalarConst_pos := by norm_num
      rowConst_nonneg := hC.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact c3FinalResidualForwardKernel_nonneg n b
  · intro n hn
    have hn3 : 3 ≤ n := (le_max_left 3 N).trans hn
    exact (c3ActualFinalResidualRatio_le_forwardRow_of_sufficientHead
      hChief hWeight  hindex published8 h18 n hn3).trans_eq (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 3 N).trans hn)


end SymmetricSubgroupAsymptotics

end


/-! The separate actual primitive10/12 high sector is exponentially
contractive. It uses only a finite literal action index, the proved complete
semisimple source, the existing outer-factor estimate and coarse subgroup
estimate. Every original quotient axis and the untouched C3 complement are
retained; there is no high-owner estimate premise. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.C3HighSemisimpleForward
open Non2UnipotentPrefixFiniteMenu

theorem physical_of_sufficientHead
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification) :
    GrowingQuotientPhysicalBound ratio 10 coefficient divisor degree
      (fun _ _ => 0) delta cutoff cutoff := by
  apply growingQuotientPhysicalBound_of_local ratio 10 (by decide) sector action predicate
    coefficient divisor degree (fun _ _ => 0) delta cutoff cutoff
    (Filter.Eventually.of_forall (fun _ => le_rfl)) ?_ ?_
  · intro n G hG
    obtain ⟨j,hn,hmem⟩ := c3PhysicalHighSemisimpleOwner_finiteFusionCover_of_sufficientHead hindex published8 G hG
    let w := c3SemisimpleHighWidth j.1
    have hw : w=10 ∨ w=12 := by
      dsimp [w,c3SemisimpleHighWidth]
      split <;> simp
    let i : Index w := ⟨c3HighSemisimpleAction j,hw,⟨c3HighSemisimpleCompression j⟩⟩
    let k : GrowingQuotientPhysicalIndex (ι := Index) 10 n :=
      ⟨⟨w,Finset.mem_Ico.mpr ⟨by rcases hw with h|h <;> omega,by omega⟩⟩,i⟩
    exact ⟨k,hmem⟩
  · apply growingQuotientLocalPhysicalBound_of_completeSource 10 action predicate source
      coefficient divisor degree (fun _ _ => 0) delta cutoff cutoff
      (fun w i => (data w i).paddedAction)
      (fun w i => (data w i).paddedAction_injective)
      (fun _ _ _ _ _ _ => trivial)
      (fun w i b => (data w i).coefficient_nonneg b)
      (fun _ _ => rfl) (fun _ _ => by simp) ?_
    intro w i b J
    exact (data w i).source_bound b (predicate w i b) J

/-- Complete actual-sector forward estimate with no unproved owner premise. -/

def forwardEstimate_of_sufficientHead
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate ratio :=
  growingQuotient_exponentialForwardEstimate ratio 10 coefficient divisor degree
    (fun _ _ => 0) delta cutoff cutoff
    (by norm_num [preE7CharacterRho]) (by norm_num [preE7CharacterRho]) (by decide)
    (fun w i b => (data w i).coefficient_nonneg b)
    (fun w i => lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (divisor_one_le w i))
    parameters (mass hOuter) hcoarse (physical_of_sufficientHead hindex published8)


end SymmetricSubgroupAsymptotics.C3HighSemisimpleForward


/-! The complete original c=1 family splits into the unchanged old physical
owner sector, the new actual semisimple sector, and the direct/low residual
sector. All three forward estimates are proved, with the complete subgroup,
normal axes, original complement degree and benchmark weights retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

def c3CompleteOrdinary_closedExponentialForwardEstimate_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : Non2UnipotentPrefixFiniteMenu.SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate c3CompleteOrdinaryRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
      (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
        (c3PhysicalStructuralOwner_closedExponentialForwardEstimate_of_sufficientHead
          hChief hWeight  hindex published8 h18 hKP)
        (C3HighSemisimpleForward.forwardEstimate_of_sufficientHead hindex published8 hOuter hcoarse))
      (c3ActualFinalResidual_exponentialForwardEstimate_of_sufficientHead
        hChief hWeight  hindex published8 h18))
    3 c3CompleteOrdinaryRatio_le_three_sectors


end SymmetricSubgroupAsymptotics
