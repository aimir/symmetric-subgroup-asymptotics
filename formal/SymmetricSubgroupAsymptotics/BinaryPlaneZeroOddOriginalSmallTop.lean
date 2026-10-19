import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSectionHeads
import SymmetricSubgroupAsymptotics.OriginalKernelSmallTopQuotientDimension

/-! On an actual original zero-odd/no-pair quartet axis whose retained
linear top has order at most two, the SAME full quotient has order at
most eight. No assertion is made about the full original group order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSmallTop
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open OriginalKernelModuleChart

theorem quotient_card_le_eight (U : Subgroup (Equiv.Perm (Fin 16)))
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
    (hj : Function.Injective j) (N : Subgroup U) [N.Normal]
    (hsmall : Nat.card (U ⧸ (pi.ker ⊔ N))≤2) : Nat.card (U ⧸ N)≤8 := by
  letI : Finite A := Finite.of_injective j hj
  obtain ⟨a,hac,_hrow,hbinary⟩ := BinaryPlaneZeroOddOriginalSectionHeads.heads U C rho pi hpi
    hlinear pointChart hpoint hzero heven hNoPair A E j hj N
  let s := sectionTop pi N hpi
  have hc : Nat.card (U ⧸ (pi.ker ⊔ N))=1 ∨
      Nat.card (U ⧸ (pi.ker ⊔ N))=2 := by
    have hp : 0<Nat.card (U ⧸ (pi.ker ⊔ N)) := Nat.card_pos
    omega
  have hsa : s a=1 := by
    rcases hc with hc | hc
    · simpa only [hc,pow_one] using (pow_card_eq_one' (x := s a))
    · have h2 : (s a)^2=1 := by simpa only [hc] using (pow_card_eq_one' (x := s a))
      have h3 : (s a)^3=1 := by rw [← map_pow,hac,map_one]
      have he : (s a)^3=s a := by rw [pow_succ,h2,one_mul]
      exact he.symm.trans h3
  have hdim : Module.finrank (ZMod 2) (E.sectionModule pi A N)≤2 := by
    apply hbinary
    change (E.sectionRepresentation pi A N).ρ (s a)=1
    rw [hsa,map_one]
  exact E.quotient_card_le_eight_of_section_dimension pi A N hdim hsmall

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSmallTop
