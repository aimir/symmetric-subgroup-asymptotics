import SymmetricSubgroupAsymptotics.CFSGTitsMiddleWeylRecovery
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveIntersectionNormalizer

/-! A concrete intrinsic normal 2-layer in the Tits middle join. Its
positive normalization is transported from the SAME original strict
kernel; middle-Weyl normalization follows from its involution relation.
No maximality, 2-core recognition, head dimension, or Out bound is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleRadical
open CFSGTitsMiddleWeylRecovery CFSGTitsAmbientPairAlignment
open CFSGReeFFourMiddlePositiveIntersectionNormalizer
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourBinaryDerivedGeneration
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev D := commutator (originalModelFixed 0)
private def pi : D →* CFSG.Models.Tits := derivedReeHom 0
private def wSource : D := ⟨middleFixedWeyl 0,middle_weyl_mem_derived 0⟩
private theorem middleWeylRoot_eq_image : middleWeylRoot=pi wSource := rfl

private theorem restricted_intersection {G : Type*} [Group G]
    (N U : Subgroup G) (w : N) :
    (U⊓U.comap (MulAut.conj (w : G)).toMonoidHom).comap N.subtype=
      U.comap N.subtype⊓(U.comap N.subtype).comap (MulAut.conj w).toMonoidHom := by
  ext x
  rfl

private theorem image_intersection {G H : Type*} [Group G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G) (U I : Subgroup G) (V : Subgroup H)
    (w : G) (v : H) (hU : IsPGroup p U)
    (hI : I=U⊓U.comap (MulAut.conj w).toMonoidHom)
    (hV : U.map f=V) (hw : f w=v) :
    I.map f=V⊓V.comap (MulAut.conj v).toMonoidHom := by
  have hC := hU.comap_of_injective (MulAut.conj w).toMonoidHom
    (MulAut.conj w).injective
  rw [hI,CentralKernelPIntersectionMap.map_inf f P hP hker U
    (U.comap (MulAut.conj w).toMonoidHom) hU hC,
    ConjugateIntersectionFunctor.map_comap_conjugate,hV,hw]

def sourceIntersection : Subgroup D :=
  (middlePositiveIntersection 0).comap D.subtype

def middleRadical : Subgroup CFSG.Models.Tits :=
  (titsPositiveSylow : Subgroup CFSG.Models.Tits)⊓
    (titsPositiveSylow : Subgroup CFSG.Models.Tits).comap
      (MulAut.conj middleWeylRoot).toMonoidHom

def middleCarrier : Subgroup CFSG.Models.Tits :=
  (titsPositiveSylow : Subgroup CFSG.Models.Tits)⊔Subgroup.zpowers middleWeylRoot

theorem sourceIntersection_image :
    Subgroup.map (G := D) (N := CFSG.Models.Tits) pi sourceIntersection=middleRadical := by
  have hI : sourceIntersection=derivedPositive 0⊓
      (derivedPositive 0).comap (MulAut.conj wSource).toMonoidHom :=
    restricted_intersection D (fixedPositive 0) wSource
  have hU : IsPGroup 2 (derivedPositive 0) := by
    rw [←positiveSylow_coe]
    exact (positiveSylow 0).isPGroup'
  exact image_intersection (G := D) (H := CFSG.Models.Tits)
    pi (positiveSylow 0) positive_quotient_injective (le_of_eq (derivedReeHom_ker 0))
    (derivedPositive 0) sourceIntersection (titsPositiveSylow : Subgroup CFSG.Models.Tits)
    wSource middleWeylRoot hU hI titsPositiveSylow_coe.symm middleWeylRoot_eq_image.symm

private theorem source_positive_normalizes :
    derivedPositive 0≤Subgroup.normalizer (sourceIntersection : Set D) := by
  intro x hx
  exact (middlePositiveIntersection 0).le_normalizer_comap D.subtype
    (positive_le_normalizer_middle_intersection 0 hx)

theorem positive_le_radical_normalizer :
    (titsPositiveSylow : Subgroup CFSG.Models.Tits)≤
      Subgroup.normalizer (middleRadical : Set CFSG.Models.Tits) := by
  have h := (Subgroup.map_mono (f := pi) source_positive_normalizes).trans
    (sourceIntersection.le_normalizer_map pi)
  have hP : (derivedPositive 0).map pi=(titsPositiveSylow : Subgroup CFSG.Models.Tits) :=
    titsPositiveSylow_coe.symm
  rw [hP,sourceIntersection_image] at h
  exact h

theorem middleCarrier_le_radical_normalizer :
    middleCarrier≤Subgroup.normalizer (middleRadical : Set CFSG.Models.Tits) :=
  sup_le positive_le_radical_normalizer (Subgroup.zpowers_le.mpr
    (CyclicFourInvolutionIntersection.normalizes_intersection
      (titsPositiveSylow : Subgroup CFSG.Models.Tits) middleWeylRoot middleWeylRoot_square))

theorem middleRadical_isPGroup : IsPGroup 2 middleRadical :=
  titsPositiveSylow.isPGroup'.of_injective (Subgroup.inclusion
    (show middleRadical≤(titsPositiveSylow : Subgroup CFSG.Models.Tits) from inf_le_left))
    (Subgroup.inclusion_injective inf_le_left)

theorem middleRadical_normal_in_carrier : (middleRadical.subgroupOf middleCarrier).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show middleRadical≤middleCarrier from inf_le_left.trans le_sup_left)).mpr
      middleCarrier_le_radical_normalizer

theorem pairStabilizer_preserves_middleRadical (f : pairStabilizer) :
    middleRadical.map f.val.toMonoidHom=middleRadical :=
  ConjugateIntersectionFunctor.invariant_intersection f.val
    (titsPositiveSylow : Subgroup CFSG.Models.Tits) middleWeylRoot
    ((mem_pairStabilizer f.val).mp f.property).1 (pairStabilizer_fixes_middleWeylRoot f)

theorem pairStabilizer_preserves_middleCarrier (f : pairStabilizer) :
    middleCarrier.map f.val.toMonoidHom=middleCarrier := by
  have hP := ((mem_pairStabilizer f.val).mp f.property).1
  have hz : (Subgroup.zpowers middleWeylRoot).map f.val.toMonoidHom=
      Subgroup.zpowers middleWeylRoot :=
    (MonoidHom.map_zpowers f.val.toMonoidHom middleWeylRoot).trans
      (congrArg Subgroup.zpowers (pairStabilizer_fixes_middleWeylRoot f))
  change ((titsPositiveSylow : Subgroup CFSG.Models.Tits)⊔Subgroup.zpowers middleWeylRoot).map
    f.val.toMonoidHom=_
  rw [Subgroup.map_sup,hP,hz]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleRadical
