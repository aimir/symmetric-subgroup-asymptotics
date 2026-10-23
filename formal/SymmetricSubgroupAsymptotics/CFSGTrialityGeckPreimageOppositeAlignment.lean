import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageRawCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGConjugateComap

/-! The actual fixed-matrix alignment restricts to the SAME derived
image preimage. Only its genuine positive Sylow is required to cover
fixed U; the whole preimage is never equated with all fixed matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageOppositeAlignment
open CFSGTrialityGeckPreimageRawCoordinates CFSGTrialityGeckDerivedSylowNormalizer
open CFSGTrialityGeckFixedPositiveRaw CFSGTrialityGeckFixedBruhatOppositeAlignment
open CFSGTrialityGeckRelativeRootGenerated CFSGConjugateComap
open CFSGSubgroupConjugateRestriction CFSGSerreOrdinaryTwists

private theorem restrict_alignment {G H : Type*} [Group G] [Group H]
    (i : G→*H) (hi : Function.Injective i) (U : Subgroup G) (R S : Subgroup H)
    (hU : U.map i=R)
    (halign : ∀g : G,R⊓R.map (MulAut.conj (i g)).toMonoidHom=⊥→
      ∃u∈R,R.map (MulAut.conj (i g)).toMonoidHom=S.map (MulAut.conj u).toMonoidHom)
    (g : G) (hdisj : U⊓U.map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈U,U.map (MulAut.conj g).toMonoidHom=(S.comap i).map (MulAut.conj b).toMonoidHom := by
  have hraw : R⊓R.map (MulAut.conj (i g)).toMonoidHom=⊥ := by
    have hh := congrArg (fun T : Subgroup G=>T.map i) hdisj
    dsimp only at hh
    rwa [Subgroup.map_inf _ _ _ hi,map_conjugate,hU,Subgroup.map_bot] at hh
  obtain ⟨u,hu,he⟩ := halign g hraw
  have huim : u∈U.map i := hU.symm ▸ hu
  obtain ⟨b,hb,hbu⟩ := huim
  have hc : R.comap i=U := by
    rw [←hU,Subgroup.comap_map_eq_self_of_injective (f := i) hi]
  rw [←hbu] at he
  have hh := congrArg (fun T : Subgroup H=>T.comap i) he
  dsimp only at hh
  rw [comap_conjugate,comap_conjugate,hc] at hh
  exact ⟨b,hb,hh⟩

def preimageNegative (q : CFSG.PrimePower) : Subgroup (naturalDerivedPreimage q) :=
  (signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true).comap (preimageRawInclusion q)

theorem preimage_opposite_conjugate_by_positive (q : CFSG.PrimePower)
    (g : naturalDerivedPreimage q)
    (hdisj : (preimageSylow q : Subgroup (naturalDerivedPreimage q))⊓
      (preimageSylow q : Subgroup (naturalDerivedPreimage q)).map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(preimageSylow q : Subgroup (naturalDerivedPreimage q)),
      (preimageSylow q : Subgroup (naturalDerivedPreimage q)).map (MulAut.conj g).toMonoidHom=
        (preimageNegative q).map (MulAut.conj b).toMonoidHom := by
  apply restrict_alignment (preimageRawInclusion q) (preimageRawInclusion_injective q)
    (preimageSylow q : Subgroup (naturalDerivedPreimage q)) (fixedPositiveRaw q)
    (signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true)
    (preimageSylow_raw_image q) ?_ g hdisj
  intro a ha
  exact fixed_opposite_conjugate_by_positive q (preimageRawInclusion q a)
    (preimageRawInclusion_mem_matrixGroup q a) (preimageRawInclusion_fixed q a) ha

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageOppositeAlignment
