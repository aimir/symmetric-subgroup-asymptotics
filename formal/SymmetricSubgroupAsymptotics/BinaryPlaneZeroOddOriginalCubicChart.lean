import SymmetricSubgroupAsymptotics.BinaryPlaneActualRegularBinaryGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulNoPairCubicLocal
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopOperatorChart
import SymmetricSubgroupAsymptotics.BinaryPlaneCubicBinaryChart
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyAugmentations

/-! The actual original no-pair zero-odd branch has the CUBIC twisted
chart, with actual two regular involutions belonging to the SAME normal
Klein lift. All section head inputs can therefore be bound together. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalCubicChart
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular top)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open BinaryPlaneActualRegularBinaryGauge (Space)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
open BinaryTwistedQuartetLoewyCoordinates (cycleAction flipAction)
open BinaryTwistedQuartetLoewyAugmentations (secondFlip)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private def second : Equiv.Perm (Fin 4) := Equiv.swap 0 2*Equiv.swap 1 3
private theorem cycle_even : cycle∈alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign cycle=1
  decide +kernel
private theorem cycle_cube : cycle^3=1 := by decide +kernel
private theorem cycle_zero : cycle 0=0 := by decide +kernel
private theorem base_zero : label 1=(0 : Fin 4) := by decide +kernel
private theorem cycle_inverse : ∀ i : Fin 4, cycle⁻¹ i=![0,3,1,2] i := by decide +kernel
private theorem flip_inverse : ∀ i : Fin 4,
    AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i=![3,2,1,0] i := by decide +kernel
private theorem second_inverse : ∀ i : Fin 4, second⁻¹ i=![2,3,0,1] i := by decide +kernel
private theorem flip_regular : ∃ r : R,
    regular r=AlternatingFourBinaryActualPolynomialUniform.flip := by decide +kernel
private theorem second_regular : ∃ r : R, regular r=second := by decide +kernel

theorem exists_chart (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame) (rho : U →* Affine) (pi : U →* C)
    (hlinear : ∀ u : U, (rho u).right=(pi u : Frame))
    (pointChart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, pointChart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (pointChart p))
    (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame U (Fin 8))) :
    ∃ (l : R →* C) (F : Space ≃ₗ[ZMod 2] Space) (a t s : C),
      l.range.Normal ∧ (∀ r, top C (l r)=regular r) ∧
      a^3=1 ∧ t∈l.range ∧ s∈l.range ∧
      (∀ v, BinaryPlaneFaithfulTopOperatorChart.representation C F a v=cycleAction v) ∧
      (∀ v, BinaryPlaneFaithfulTopOperatorChart.representation C F t v=flipAction v) ∧
      (∀ v, BinaryPlaneFaithfulTopOperatorChart.representation C F s v=secondFlip v) := by
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
    pointChart hpoint hzero heven hNoPair
  obtain ⟨l,hl,hn,ht⟩ := BinaryPlaneFaithfulTopRegularLift.exists_lift C hinj heven
  letI : l.range.Normal := hn
  have htop : ∀ r, (l r : Frame).right=regular r := ht
  obtain ⟨a,ha⟩ := heven ⟨cycle,cycle_even⟩
  have hac : a^3=1 := hinj (by
    rw [map_pow,map_one]
    change (a : Frame).right^3=1
    rw [ha]
    exact cycle_cube)
  let L := (a : Frame).left (label 1)
  have hLn : L≠1 := by
    change (a : Frame).left (label 1)≠1
    rw [base_zero]
    exact BinaryPlaneFaithfulNoPairCubicLocal.nontrivial U C rho pi hlinear
      pointChart hpoint hinj heven hNoPair a ha
  have hLc : L^3=1 := by
    let q : BinaryPlaneZeroOddDichotomy.stabilizer C := ⟨a,by
      change (a : Frame).right 0=0
      rw [ha]
      exact cycle_zero⟩
    have hq : q^3=1 := Subtype.ext hac
    have hh := congrArg (BinaryPlaneZeroOddDichotomy.localStabilizer C) hq
    simpa only [map_pow,map_one,BinaryPlaneZeroOddDichotomy.localStabilizer,
      q,L,base_zero] using hh
  obtain ⟨E,hE⟩ := BinaryPlaneCubicBinaryChart.exists_chart L hLc hLn
  let F : Space ≃ₗ[ZMod 2] Space :=
    (BinaryPlaneActualRegularBinaryGauge.chart C l).trans
      (LinearEquiv.piCongrRight (fun _ => E))
  obtain ⟨rt,hrt⟩ := flip_regular
  obtain ⟨rs,hrs⟩ := second_regular
  refine ⟨l,F,a,l rt,l rs,hn,ht,hac,⟨rt,rfl⟩,⟨rs,rfl⟩,?_,?_,?_⟩
  · intro v
    funext i
    change E (BinaryPlaneActualRegularBinaryGauge.chart C l
      (BinaryPlaneCyclicWreathUniform.representation C a (F.symm v)) i)=_
    rw [BinaryPlaneActualRegularBinaryGauge.normalizer_action C l htop a ha]
    change E (L (BinaryPlaneActualRegularBinaryGauge.chart C l (F.symm v) (cycle⁻¹ i)))=_
    rw [hE]
    change BinaryTwistedQuartetPolynomial.cubic (F (F.symm v) (cycle⁻¹ i))=_
    rw [F.apply_symm_apply,cycle_inverse]
    fin_cases i <;> rfl
  · intro v
    funext i
    change E (BinaryPlaneActualRegularBinaryGauge.chart C l
      (BinaryPlaneCyclicWreathUniform.representation C (l rt) (F.symm v)) i)=_
    rw [BinaryPlaneActualRegularBinaryGauge.regular_action C l htop,hrt]
    change F (F.symm v) (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i)=_
    rw [F.apply_symm_apply,flip_inverse]
    fin_cases i <;> rfl
  · intro v
    funext i
    change E (BinaryPlaneActualRegularBinaryGauge.chart C l
      (BinaryPlaneCyclicWreathUniform.representation C (l rs) (F.symm v)) i)=_
    rw [BinaryPlaneActualRegularBinaryGauge.regular_action C l htop,hrs]
    change F (F.symm v) (second⁻¹ i)=_
    rw [F.apply_symm_apply,second_inverse]
    fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalCubicChart
