import SymmetricSubgroupAsymptotics.AlternatingSignedImageNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Zero LOCAL odd kernel still permits nonbinary A4/S4 top. The actual
linear image embeds in the sign wreath and has allnormal bound two.
This does not by itself bound its binary affine translation extension. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingZeroOddLinearSocles
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel

theorem normal_generating_pairs (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hzero : oddKernel C=⊥) :
    ∀ N : Subgroup C, N.Normal →
      ∃ x : Fin 2 → C, Subgroup.normalClosure (Set.range x)=N := by
  let f := signProjection C
  have hf : Function.Injective f := f.ker_eq_bot_iff.mp hzero
  let B := f.range
  let E : C ≃* B := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have ht : alternatingGroup (Fin 4)≤AlternatingSignedImageNormalGenerators.blockImage B := by
    intro p hp
    obtain ⟨g,hg⟩ := heven ⟨p,hp⟩
    exact ⟨f.rangeRestrict g,hg⟩
  exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
    (AlternatingSignedImageNormalGenerators.normal_generating_pairs B ht)

theorem quotientSocle (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hzero : oddKernel C=⊥) (N : Subgroup C) [N.Normal] :
    SocleNormalGeneratorBound (C ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_pairs C heven hzero) N

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingZeroOddLinearSocles
