import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSectionHeads
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalSmallTop
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulBinaryQuotientOrder

/-! On an actual original zero-odd/no-pair quartet axis whose retained
linear top has order at most two, the SAME full quotient has order at
most eight. No assertion is made about the full original group order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalBinaryQuotient
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
    (hbinary : IsPGroup 2 (U ⧸ N)) : Nat.card (U ⧸ N)≤8 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
    pointChart hpoint hzero heven hNoPair
  obtain ⟨l,hli,_hln,ht⟩ := BinaryPlaneFaithfulTopRegularLift.exists_lift C hinj heven
  have hlcard : Nat.card l.range=4 := by
    let e := MulEquiv.ofBijective l.rangeRestrict
      ⟨fun x y h => hli (congrArg Subtype.val h),l.rangeRestrict_surjective⟩
    rw [← Nat.card_congr e.toEquiv]
    change Nat.card (Multiplicative (Fin 2 → ZMod 2))=4
    rw [Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (Fin 2 → ZMod 2) ≃ (Fin 2 → ZMod 2))]
    simp
  have hb : IsPGroup 2 (U ⧸ (pi.ker ⊔ N)) :=
    hbinary.of_surjective (base pi N) (base_surjective pi N)
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hb
  have hs : Function.Surjective (sectionTop pi N hpi) := by
    intro x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) x
    exact ⟨pi u,sectionTop_apply pi N hpi u⟩
  have hsmall := BinaryPlaneFaithfulBinaryQuotientOrder.card_le_two C hinj heven
    l ht hlcard (sectionTop pi N hpi) hs n hn
  exact BinaryPlaneZeroOddOriginalSmallTop.quotient_card_le_eight U C rho pi hpi hlinear
    pointChart hpoint hzero heven hNoPair A E j hj N hsmall

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalBinaryQuotient
