import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveAssociatedMiddle
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom

/-! Exact positive-kernel recognition in the SAME actual middle
parabolic, for every field parameter. Actual fixed sign factorization
and the faithful actual middle block remove the middle factor. This is
not an assertion that the whole kernel lies in the derived subgroup or
that an intrinsic normal 2-core has already been recognized. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveKernelIntersection
open CFSGReeFFourFixedPositiveAssociatedMiddle CFSGReeFFourMiddleAssociatedQuotient
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourMiddleParabolicFlag
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFixedSubgroupPeeling CFSGReeFFourFixedBruhatCover
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourMiddleFixedInversion
open CFSGGradedMatrixAssociatedUnitHom CFSGGradedMatrixSubgroups
open CFSGReeFFourFieldParameters CFSGReeFFourRelativeSimpleWeyl
open CFSGOpposedSubgroupPeeling CFSGReeFFourFixedAmbientHom
open CFSGFFourOriginalMiddleWords

private theorem kernel_from_factorization {G C : Type*} [Group G] [Group C]
    (f : G →* C) (U B : Subgroup G) (w : G)
    (hB : Function.Injective (f.comp B.subtype))
    (hI : U⊓U.comap (MulAut.conj w).toMonoidHom≤f.ker)
    (hfac : ∀u∈U,∃a∈U⊓U.comap (MulAut.conj w).toMonoidHom,
      ∃b∈B,u=a*b) :
    U⊓f.ker=U⊓U.comap (MulAut.conj w).toMonoidHom := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a,ha,b,hb,he⟩ := hfac u hu.1
    have hfa : f a=1 := hI ha
    have hfb : f b=1 := by
      have hz : f (a*b)=1 := (congrArg f he).symm.trans hu.2
      simpa only [map_mul,hfa,one_mul] using hz
    have hb1 : b=1 := congrArg (fun z : B => (z : G))
      (hB (show f.comp B.subtype ⟨b,hb⟩=f.comp B.subtype 1 from
        hfb.trans (map_one f).symm))
    have hua : u=a := by simpa only [hb1,mul_one] using he
    exact hua.symm ▸ ha
  · intro u hu
    exact ⟨hu.1,hI hu⟩

private theorem paired_middle_eq (m : ℕ) : fixedPairedWord m [true]=middleFixedWeyl m := by
  apply Subtype.ext
  simpa only [if_true] using CFSGReeFFourSimpleInversionBlocks.single_paired_word_val m true

private def middleWeylInParabolic (m : ℕ) : middleParabolic m :=
  ⟨middleFixedWeyl m,(show Subgroup.closure {middleFixedWeyl m}≤middleParabolic m from le_sup_right)
    (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl))⟩

def positiveInParabolic (m : ℕ) : Subgroup (middleParabolic m) :=
  (fixedPositive m).comap (middleParabolic m).subtype

private def middleInParabolic (m : ℕ) : Subgroup (middleParabolic m) :=
  (middleFixedSubgroup m).comap (middleParabolic m).subtype

private theorem associated_injective_middle (m : ℕ) :
    Function.Injective ((middleAssociatedHom m).comp (middleInParabolic m).subtype) := by
  intro x y he
  change middleAssociatedHom m x.val=middleAssociatedHom m y.val at he
  have hx : middleAssociatedHom m x.val=fixedRawHom m x.val.val :=
    associatedUnit_eq_of_preserving middleWeight (parabolicToTriangular m x.val)
      (middleFixed_raw_preserving m x.val.val x.property)
  have hy : middleAssociatedHom m y.val=fixedRawHom m y.val.val :=
    associatedUnit_eq_of_preserving middleWeight (parabolicToTriangular m y.val)
      (middleFixed_raw_preserving m y.val.val y.property)
  have hraw : fixedRawHom m x.val.val=fixedRawHom m y.val.val := hx.symm.trans (he.trans hy)
  have hg : x.val.val=y.val.val := Subtype.ext (rawHom_injective (Field m) hraw)
  exact Subtype.ext (Subtype.ext hg)

private theorem intersection_le_kernel (m : ℕ) :
    positiveInParabolic m⊓(positiveInParabolic m).comap
      (MulAut.conj (middleWeylInParabolic m)).toMonoidHom≤(middleAssociatedHom m).ker := by
  intro x hx
  rw [middleAssociatedHom_ker]
  exact fixedPositive_remainder_strict m x.val hx.1 hx.2

private theorem positive_factorization (m : ℕ) (u : middleParabolic m)
    (hu : u∈positiveInParabolic m) :
    ∃a∈positiveInParabolic m⊓(positiveInParabolic m).comap
      (MulAut.conj (middleWeylInParabolic m)).toMonoidHom,
      ∃b∈middleInParabolic m,u=a*b := by
  obtain ⟨a,ha,b,hb,he,hwa⟩ := fixed_sign_factorization m [true] u.val hu
  have hblock : inversionPart (fixedPositive m)
      (CFSGReeFFourOppositionFixedPositiveNegative.fixedNegative m)
      (fixedPairedWord m [true])=middleFixedSubgroup m :=
    (simple_inversion_eq_block m true).trans (fixedMiddleInversion_eq_middleFixedSubgroup m)
  rw [hblock] at hb
  rw [paired_middle_eq] at hwa
  let A : middleParabolic m := ⟨a,positive_le_parabolic m ha⟩
  let B : middleParabolic m := ⟨b,positive_le_parabolic m
    (middleFixedSubgroup_le_fixedPositive m hb)⟩
  refine ⟨A,⟨ha,hwa⟩,B,hb,Subtype.ext he⟩

theorem positive_kernel_eq_intersection (m : ℕ) :
    positiveInParabolic m⊓(middleAssociatedHom m).ker=
      positiveInParabolic m⊓(positiveInParabolic m).comap
        (MulAut.conj (middleWeylInParabolic m)).toMonoidHom :=
  kernel_from_factorization (middleAssociatedHom m) (positiveInParabolic m)
    (middleInParabolic m) (middleWeylInParabolic m) (associated_injective_middle m)
    (intersection_le_kernel m) (positive_factorization m)

theorem positive_strict_iff_opposite_positive (m : ℕ) (u : originalModelFixed m)
    (hu : u∈fixedPositive m) :
    fixedRawHom m u∈strictUnits middleWeight ↔
      middleFixedWeyl m*u*(middleFixedWeyl m)⁻¹∈fixedPositive m := by
  let U : middleParabolic m := ⟨u,positive_le_parabolic m hu⟩
  have h := congrArg (fun V : Subgroup (middleParabolic m) => U∈V)
    (positive_kernel_eq_intersection m)
  have he : (U∈positiveInParabolic m ∧ U∈(middleAssociatedHom m).ker) ↔
      (U∈positiveInParabolic m ∧
        U∈(positiveInParabolic m).comap (MulAut.conj (middleWeylInParabolic m)).toMonoidHom) :=
    Iff.of_eq h
  have hp : U∈positiveInParabolic m := hu
  constructor
  · intro hs
    have hk : U∈(middleAssociatedHom m).ker := by
      rw [middleAssociatedHom_ker]
      exact hs
    exact (he.mp ⟨hp,hk⟩).2
  · intro hc
    have hk := (he.mpr ⟨hp,hc⟩).2
    rw [middleAssociatedHom_ker] at hk
    exact hk

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveKernelIntersection
