import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalCubicChart
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalSocleCoinvariance
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualSectionHead

/-! Literal original-N section heads in the genuine zero-odd/no-pair
quartet branch. Actual chart, actual monolith and actual original section
maps are assembled without operator or numerical-capacity premises. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSectionHeads
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open OriginalKernelModuleChart

set_option maxHeartbeats 500000 in
theorem heads (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame) (rho : U →* Affine) (pi : U →* C)
    (hpi : Function.Surjective pi)
    (hlinear : ∀ u : U, (rho u).right=(pi u : Frame))
    (pointChart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, pointChart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (pointChart p))
    (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame U (Fin 8)))
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j) (N : Subgroup U) [N.Normal] :
    let tau := (E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N hpi)
    ∃ a : C, a^3=1 ∧
      (finiteGroupSocle (U ⧸ N)≤(base pi N).ker ∨
        Module.finrank (ZMod 2) (LinearMap.range (tau a+(tau a)^2))≤2) ∧
      (tau a=1 → Module.finrank (ZMod 2) (E.sectionModule pi A N)≤2) := by
  let tau := (E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N hpi)
  obtain ⟨l,F,a,t,s,hn,ht,hac,htmem,hsmem,ha,hT,hS⟩ :=
    BinaryPlaneZeroOddOriginalCubicChart.exists_chart U C rho pi hlinear pointChart hpoint
      hzero heven hNoPair
  let beta := BinaryPlaneFaithfulTopOperatorChart.representation C F
  let inter : Representation.IntertwiningMap
      (BinaryPlaneCyclicWreathUniform.representation C) beta := {
    toLinearMap := F.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro v
      change F (BinaryPlaneCyclicWreathUniform.representation C h v)=
        F (BinaryPlaneCyclicWreathUniform.representation C h (F.symm (F v)))
      rw [F.symm_apply_apply] }
  let jF := inter.comp j
  have hjF : Function.Injective jF := F.injective.comp hj
  let q := E.sectionProjectionOnBase pi A N hpi
  have hq : Function.Surjective q := E.sectionProjectionOnBase_surjective pi A N hpi
  have hbinary : tau a=1 → Module.finrank (ZMod 2) (E.sectionModule pi A N)≤2 := by
    intro hqa
    exact BinaryTwistedQuartetActualSectionHead.section_trivial beta a ha tau A.ρ
      jF hjF q hq hqa
  refine ⟨a,hac,?_,hbinary⟩
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
    pointChart hpoint hzero heven hNoPair
  rcases BinaryPlaneFaithfulOriginalSocleCoinvariance.dichotomy C hinj heven l ht
      pi hpi A E N with hinside | hcoin
  · exact Or.inl hinside
  · right
    have hqt : tau t=1 := congrArg Units.val (hcoin htmem)
    have hqs : tau s=1 := congrArg Units.val (hcoin hsmem)
    exact BinaryTwistedQuartetActualSectionHead.section_nontrivial beta a t s ha hT hS tau
      A.ρ jF hjF q hq hqt hqs

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSectionHeads
