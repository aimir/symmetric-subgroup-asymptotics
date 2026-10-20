import SymmetricSubgroupAsymptotics.AlternatingTopImageNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopRegularLift
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! A faithful actual quartet top has normally cyclic linear image and
all its actual quotient socles have bound one. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopLinearSocles
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)

theorem normal_generating_singletons (C : Subgroup Frame)
    (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∀ N : Subgroup C, N.Normal →
      ∃ x : Fin 1 → C, Subgroup.normalClosure (Set.range x)=N := by
  let E : C ≃* (top C).range := MulEquiv.ofBijective (top C).rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h),(top C).rangeRestrict_surjective⟩
  have ht : alternatingGroup (Fin 4)≤(top C).range := by
    intro p hp
    exact heven ⟨p,hp⟩
  exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
    (AlternatingTopImageNormalGenerators.normal_generating_singletons (top C).range ht)

theorem quotientSocle (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (N : Subgroup C) [N.Normal] : SocleNormalGeneratorBound (C ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_singletons C hinj heven) N

theorem socle_of_surjective (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    {D : Type} [Group D] (phi : C →* D) (hphi : Function.Surjective phi) :
    SocleNormalGeneratorBound D 1 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective phi hphi)
    (quotientSocle C hinj heven phi.ker)

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopLinearSocles
