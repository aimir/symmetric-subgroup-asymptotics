import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneTopKernel
import SymmetricSubgroupAsymptotics.NormalGeneratorExtension
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Rank-one actual linear quartet images have all normal quotients with
whole-socle bound two: their actual top kernel is normally cyclic and
their actual block image is literally A4 or S4, also normally cyclic. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneLinearSocles
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (top)
open BinaryPlaneWreathActualOddKernel

private theorem above_alternating (B : Subgroup (Equiv.Perm (Fin 4)))
    (hAB : alternatingGroup (Fin 4)≤B) : B=alternatingGroup (Fin 4) ∨ B=⊤ := by
  have hm := Subgroup.relIndex_mul_index hAB
  rw [alternatingGroup.index_eq_two] at hm
  have hd : B.index∣2 := ⟨(alternatingGroup (Fin 4)).relIndex B,
    by simpa only [Nat.mul_comm] using hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · left
    have hr : (alternatingGroup (Fin 4)).relIndex B=1 := by
      rw [h] at hm
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hr) hAB

private theorem top_singletons (B : Subgroup (Equiv.Perm (Fin 4)))
    (hAB : alternatingGroup (Fin 4)≤B) :
    ∀ N : Subgroup B, N.Normal →
      ∃ x : Fin 1 → B, Subgroup.normalClosure (Set.range x)=N := by
  rcases above_alternating B hAB with h | h
  · let E := MulEquiv.subgroupCongr h
    exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.alternating_normal_total)
  · let E : B ≃* Equiv.Perm (Fin 4) := MulEquiv.ofBijective B.subtype
      ⟨Subtype.val_injective,fun x => ⟨⟨x,by rw [h]; trivial⟩,rfl⟩⟩
    exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.symmetric_normal_total)

theorem normal_generating_pairs (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∀ N : Subgroup C, N.Normal →
      ∃ x : Fin 2 → C, Subgroup.normalClosure (Set.range x)=N := by
  let f := (top C).rangeRestrict
  have hk : f.ker=(top C).ker := by
    ext x
    exact Subtype.ext_iff
  let E := MulEquiv.subgroupCongr hk
  have hkernel : ∀ N : Subgroup f.ker, N.Normal →
      ∃ x : Fin 1 → f.ker, Subgroup.normalClosure (Set.range x)=N :=
    normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
      (BinaryPlaneAlternatingRankOneTopKernel.normal_generating_singletons C e heven)
  have ht : alternatingGroup (Fin 4)≤(top C).range := by
    intro p hp
    obtain ⟨g,hg⟩ := heven ⟨p,hp⟩
    exact ⟨g,hg⟩
  exact normal_generating_tuples_of_kernel_and_image f (top C).rangeRestrict_surjective
    hkernel (top_singletons (top C).range ht)

theorem quotientSocle (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (N : Subgroup C) [N.Normal] : SocleNormalGeneratorBound (C ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_pairs C e heven) N

theorem socle_of_surjective (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    {D : Type} [Group D] (phi : C →* D) (hphi : Function.Surjective phi) :
    SocleNormalGeneratorBound D 2 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective phi hphi)
    (quotientSocle C e heven phi.ker)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneLinearSocles
