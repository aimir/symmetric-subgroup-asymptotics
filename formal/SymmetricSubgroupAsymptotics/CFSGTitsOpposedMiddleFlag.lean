import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleFlag

/-! The negative intrinsic flag uses the SAME already recovered internal
reflection. Opposition supplies an actual equivalence between the flags;
this is not an extension of an arbitrary target automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsOpposedMiddleFlag
open CFSGTitsIntrinsicMiddleFlag CFSGTitsCentralReflection CFSGTitsAmbientPairAlignment
open CFSGTitsNegativeCentralRoot CFSGReeFFourBinaryCentralReflection
open CFSGReeFFourBinaryPenultimateWeyl CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourMinimalParabolics
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourBinarySylowNormalizerSolvable
private abbrev D := commutator (originalModelFixed 0)
private def rSource : D := ⟨centralReflection,centralReflection_mem_derived⟩

private theorem fixes_normal_source {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (g : G) (r : N) (h : Commute g (r : G)) :
    MulAut.conjNormal g r=r := by
  apply Subtype.ext
  change g*(r : G)*g⁻¹=(r : G)
  rw [h.eq,mul_assoc,mul_inv_cancel,mul_one]

private theorem map_flag {G : Type*} [Group G] (f : MulAut G)
    (U V : Subgroup G) (r : G) (hU : U.map f.toMonoidHom=V) (hr : f r=r) :
    (U⊓U.comap (MulAut.conj r).toMonoidHom).map f.toMonoidHom=
      V⊓V.comap (MulAut.conj r).toMonoidHom := by
  rw [Subgroup.map_inf _ _ f.toMonoidHom f.injective,
    ConjugateIntersectionFunctor.map_comap_conjugate,hU]
  exact congrArg (fun x : G => V⊓V.comap (MulAut.conj x).toMonoidHom) hr

theorem opposition_commute_centralReflection :
    Commute (oppositionFixed 0) centralReflection := by
  have hw : Commute (oppositionFixed 0) (middleFixedWeyl 0) := by
    simpa only [simpleWeyl_true] using binary_opposition_commute_simple true
  change Commute (oppositionFixed 0)
    (centralConjugator*middleFixedWeyl 0*centralConjugator⁻¹)
  exact (opposition_commute_centralConjugator.mul_right hw).mul_right
    opposition_commute_centralConjugator.inv_right

theorem opposition_fixes_reflectionRoot :
    ambientAction 0 (oppositionFixed 0) reflectionRoot=reflectionRoot := by
  have hr : reflectionRoot=derivedReeHom 0 rSource := rfl
  have hs : MulAut.conjNormal (oppositionFixed 0) rSource=rSource :=
    fixes_normal_source D (oppositionFixed 0) rSource opposition_commute_centralReflection
  calc
    _=ambientAction 0 (oppositionFixed 0) (derivedReeHom 0 rSource) :=
      congrArg (ambientAction 0 (oppositionFixed 0)) hr
    _=derivedReeHom 0 (MulAut.conjNormal (oppositionFixed 0) rSource) :=
      ambientAction_apply 0 (oppositionFixed 0) rSource
    _=derivedReeHom 0 rSource := congrArg (derivedReeHom 0) hs
    _=reflectionRoot := hr.symm

def negativeIntrinsicFlag : Subgroup CFSG.Models.Tits :=
  (titsNegativeSylow : Subgroup CFSG.Models.Tits) ⊓
    (titsNegativeSylow : Subgroup CFSG.Models.Tits).comap
      (MulAut.conj reflectionRoot).toMonoidHom

theorem intrinsicFlag_map_opposition :
    intrinsicFlag.map (ambientAction 0 (oppositionFixed 0)).toMonoidHom=
      negativeIntrinsicFlag :=
  map_flag (ambientAction 0 (oppositionFixed 0))
    (titsPositiveSylow : Subgroup CFSG.Models.Tits)
    (titsNegativeSylow : Subgroup CFSG.Models.Tits) reflectionRoot
    positive_map_opposition opposition_fixes_reflectionRoot

def opposedFlagEquiv : intrinsicFlag≃*negativeIntrinsicFlag :=
  ((ambientAction 0 (oppositionFixed 0)).subgroupMap intrinsicFlag).trans
    (MulEquiv.subgroupCongr intrinsicFlag_map_opposition)

theorem pairStabilizer_preserves_negativeFlag (f : pairStabilizer) :
    negativeIntrinsicFlag.map f.val.toMonoidHom=negativeIntrinsicFlag :=
  ConjugateIntersectionFunctor.invariant_intersection f.val
    (titsNegativeSylow : Subgroup CFSG.Models.Tits) reflectionRoot
    ((mem_pairStabilizer f.val).mp f.property).2
    (pairStabilizer_fixes_reflectionRoot f)

end SymmetricSubgroupAsymptotics.CFSGTitsOpposedMiddleFlag
