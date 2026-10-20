import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalCubicProjectorHeads
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulCubicNormalImage
import SymmetricSubgroupAsymptotics.OriginalBinaryKernelCubicLift
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.OriginalElementaryImageRange
import SymmetricSubgroupAsymptotics.OriginalKernelIntersectionProjectorRanks
import SymmetricSubgroupAsymptotics.SelectedBinarySocleCubicRestriction

/-! Two binary-socle positions in the genuine original zero-odd/no-pair
outside branch. All intersection and image maps use the original N. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalOutsideSocle
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open OriginalKernelModuleChart
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

set_option maxHeartbeats 1000000 in
theorem binarySocle_bound (U : Subgroup (Equiv.Perm (Fin 16)))
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
    (hnonbinary : ¬ IsPGroup 2 (U ⧸ N))
    (houtside : ¬ finiteGroupSocle (U ⧸ N)≤(base pi N).ker) :
    MarkedC4.normalGen (minimalNormalSoclePart (U ⧸ N) (fun M => IsPGroup 2 M))≤2 := by
  letI : Finite A := Finite.of_injective j hj
  let K := E.sectionRepresentation pi A N
  letI : FiniteDimensional (ZMod 2) K := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi A N)
    infer_instance
  let b := base pi N
  let s := sectionTop pi N hpi
  let F := E.quotientChart pi A N
  have hs : Function.Surjective s := by
    intro x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) x
    exact ⟨pi u,sectionTop_apply pi N hpi u⟩
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
    pointChart hpoint hzero heven hNoPair
  have hcardB : Nat.card (U ⧸ (pi.ker ⊔ N))∣2^3*3 := by
    have hd := Subgroup.card_dvd_of_surjective s hs
    rcases BinaryPlaneFaithfulOriginalOrder.linear_card C hinj heven with hc | hc
    · exact hd.trans (by rw [hc]; norm_num)
    · exact hd.trans (by rw [hc]; norm_num)
  have hthree : 3∣Nat.card (U ⧸ (pi.ker ⊔ N)) :=
    F.three_dvd_base_of_nonbinary b K 3 hcardB hnonbinary
  obtain ⟨a,hac,han,hfixed,hrow,_⟩ :=
    BinaryPlaneZeroOddOriginalCubicProjectorHeads.projector_heads U C rho pi hpi hlinear
      pointChart hpoint hzero heven hNoPair A E j hj N
  have hactive := hrow.resolve_left houtside
  obtain ⟨g,hgc,hga⟩ := E.exists_original_cubic_lift pi A hpi a hac
  have hgn : g≠1 := by
    intro hg
    apply han
    rw [← hga,hg,map_one]
  let H := Subgroup.zpowers g
  let z : H := ⟨g,Subgroup.mem_zpowers g⟩
  have hH : Nat.card H=3 := by rw [Nat.card_zpowers,orderOf_eq_prime hgc hgn]
  letI : NeZero (Nat.card H : ZMod 2) := ⟨by rw [hH]; decide⟩
  let f : H →* U ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hzc : z^3=1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow,Subgroup.coe_one] using hgc
  have hzgen : ∀ h : H, ∃ n : ℕ, h=z^n := by
    intro h
    have hm : (h : U)∈Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr h.property
    obtain ⟨n,hn⟩ := hm
    exact ⟨n,Subtype.ext hn.symm⟩
  have hbg : b (f z)=s a := by
    change base pi N (QuotientGroup.mk' N g)=sectionTop pi N hpi a
    rw [base_apply,← hga,sectionTop_apply]
  have hOp : K.ρ (b (f z))=K.ρ (s a) := congrArg K.ρ hbg
  have hkeHead : Module.finrank (ZMod 2)
      (LinearMap.range (1+K.ρ (b (f z))+(K.ρ (b (f z)))^2))≤2 := by
    rw [hOp]
    exact hfixed
  have hkfHead : Module.finrank (ZMod 2)
      (LinearMap.range (K.ρ (b (f z))+(K.ρ (b (f z)))^2))≤2 := by
    rw [hOp]
    exact hactive
  let D := selectedPrimeSoclePartElementaryChart 2 (G := U ⧸ N) (fun _ => True)
  let J := D.originalKernelChart
  letI : FiniteDimensional (ZMod 2) D.quotientRepresentation := D.finiteDimensional
  letI : Finite D.quotientRepresentation := Module.finite_of_finite (ZMod 2)
  let L := (J.elementaryImageHom b).range
  have hL : L.Normal := J.elementaryImage_normal b (base_surjective pi N)
  have hLb : IsPGroup 2 L := J.elementaryImage_isPGroup_two b
  obtain ⟨hLc,hLf⟩ := BinaryPlaneFaithfulCubicNormalImage.property C hinj heven
    _ s hs hthree L hL hLb
  apply SelectedBinarySocleCubicRestriction.normalGen_le_two b f z hzgen hzc
  · have hh := J.kernelIntersection_fixed_projector_rank_le b F (f z)
    exact hh.trans hkeHead
  · have hh := J.kernelIntersection_active_rank_le b F (f z)
    exact hh.trans hkfHead
  · exact hLc
  · intro x hx hfix
    apply hLf a hac han x hx
    rwa [hbg] at hfix

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalOutsideSocle
