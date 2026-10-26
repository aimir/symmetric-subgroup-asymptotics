import SymmetricSubgroupAsymptotics.CFSGTitsCentralReflection
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryReflectionMiddleFlag
import SymmetricSubgroupAsymptotics.CentralKernelPIntersectionMap
import SymmetricSubgroupAsymptotics.ConjugateIntersectionFunctor

/-! The literal intrinsic intersection of the Tits positive Sylow and
its conjugate by the recovered reflection. Its original preimage flag
is identified through the FULL central quotient, by separation of all
2-elements. No automorphism is extended to the ambient fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleFlag
open CFSGTitsCentralReflection CFSGTitsAmbientPairAlignment
open CFSGReeFFourBinaryReflectionMiddleFlag CFSGReeFFourBinaryCentralReflection
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourFixedModelEquivalence
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev D := commutator (originalModelFixed 0)
private def pi : D →* CFSG.Models.Tits := derivedReeHom 0
private def rSource : D := ⟨centralReflection,centralReflection_mem_derived⟩

private theorem conjugation_restriction {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (r : N) :
    MulAut.conjNormal (r : G)=MulAut.conj r := by
  ext x
  rfl

private theorem reflectionRoot_eq_image : reflectionRoot=pi rSource := rfl

private theorem positive_two_group : IsPGroup 2 (derivedPositive 0) := by
  rw [←positiveSylow_coe]
  exact (positiveSylow 0).isPGroup'

def intrinsicFlag : Subgroup CFSG.Models.Tits :=
  (titsPositiveSylow : Subgroup CFSG.Models.Tits) ⊓
    (titsPositiveSylow : Subgroup CFSG.Models.Tits).comap
      (MulAut.conj reflectionRoot).toMonoidHom

private theorem image_intersection {G H : Type*} [Group G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G) (U I : Subgroup G) (V : Subgroup H)
    (r : G) (s : H) (hU : IsPGroup p U)
    (hI : I=U⊓U.comap (MulAut.conj r).toMonoidHom)
    (hV : U.map f=V) (hr : f r=s) :
    I.map f=V⊓V.comap (MulAut.conj s).toMonoidHom := by
  have hC := hU.comap_of_injective (MulAut.conj r).toMonoidHom
    (MulAut.conj r).injective
  rw [hI,CentralKernelPIntersectionMap.map_inf f P hP hker U
    (U.comap (MulAut.conj r).toMonoidHom) hU hC,
    ConjugateIntersectionFunctor.map_comap_conjugate,hV,hr]

theorem image_reflectionIntersection :
    Subgroup.map (G := D) (N := CFSG.Models.Tits) pi reflectionIntersection=intrinsicFlag := by
  have hc : MulAut.conjNormal centralReflection=MulAut.conj rSource :=
    conjugation_restriction (commutator (originalModelFixed 0)) rSource
  have hs : reflectionIntersection=derivedPositive 0 ⊓
      (derivedPositive 0).comap (MulAut.conj rSource).toMonoidHom := by
    rw [reflectionIntersection,hc]
  exact image_intersection (G := D) (H := CFSG.Models.Tits)
    pi (positiveSylow 0) positive_quotient_injective
    (le_of_eq (derivedReeHom_ker 0)) (derivedPositive 0) reflectionIntersection
    (titsPositiveSylow : Subgroup CFSG.Models.Tits) rSource reflectionRoot
    positive_two_group hs titsPositiveSylow_coe.symm reflectionRoot_eq_image.symm

def flagHom : reflectionIntersection →* CFSG.Models.Tits :=
  pi.comp reflectionIntersection.subtype

theorem flagHom_injective : Function.Injective flagHom := by
  intro x y h
  have hx : x.val∈derivedPositive 0 := x.property.1
  have hy : y.val∈derivedPositive 0 := y.property.1
  have he : (⟨x.val,hx⟩ : derivedPositive 0)=(⟨y.val,hy⟩ : derivedPositive 0) :=
    titsPositiveHom_injective h
  exact Subtype.ext (congrArg (fun z : derivedPositive 0 => (z : D)) he)

private theorem flagHom_range : flagHom.range=intrinsicFlag := by
  have he : flagHom.range=reflectionIntersection.map pi := by
    rw [flagHom,MonoidHom.range_comp,reflectionIntersection.range_subtype]
  exact he.trans image_reflectionIntersection

def flagEquiv : reflectionIntersection≃*intrinsicFlag :=
  (MonoidHom.ofInjective flagHom_injective).trans (MulEquiv.subgroupCongr flagHom_range)

theorem pairStabilizer_preserves_intrinsicFlag (f : pairStabilizer) :
    intrinsicFlag.map f.val.toMonoidHom=intrinsicFlag :=
  ConjugateIntersectionFunctor.invariant_intersection f.val
    (titsPositiveSylow : Subgroup CFSG.Models.Tits) reflectionRoot
    ((mem_pairStabilizer f.val).mp f.property).1
    (pairStabilizer_fixes_reflectionRoot f)

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleFlag
