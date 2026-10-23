import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositionAxes

/-! Every opposed-pair fixer of the SAME original triality group fixes
all four full simple signed relative root groups. Positive-axis recovery
uses literal opposition and the negative-axis theorem, without asserting
that opposition squares to one or lifting the original automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedRootAction
open CFSGTrialityGeckOriginalNegativeRootAction CFSGTrialityGeckOriginalNegativeRootIntersection
open CFSGTrialityGeckOriginalOppositionAxes CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalOppositeAlignment

private theorem map_aut_mul {G : Type*} [Group G] (P : Subgroup G) (f g : MulAut G) :
    P.map (f*g).toMonoidHom=(P.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_aut_inverse {G : Type*} [Group G] (P Q : Subgroup G)
    (e : MulAut G) (he : P.map e.toMonoidHom=Q) : Q.map (e⁻¹).toMonoidHom=P := by
  rw [←he,Subgroup.map_map]
  have hi : (e⁻¹).toMonoidHom.comp e.toMonoidHom=MonoidHom.id G := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [hi,Subgroup.map_id]

private theorem opposite_family_fix {G I : Type*} [Group G]
    (U V : Subgroup G) (N : I→Subgroup G) (e : MulAut G)
    (hUV : U.map e.toMonoidHom=V) (hVU : V.map e.toMonoidHom=U)
    (hfix : ∀f : MulAut G,U.map f.toMonoidHom=U→V.map f.toMonoidHom=V→
      ∀i,(N i).map f.toMonoidHom=N i)
    (f : MulAut G) (hU : U.map f.toMonoidHom=U) (hV : V.map f.toMonoidHom=V) :
    ∀i,((N i).map e.toMonoidHom).map f.toMonoidHom=(N i).map e.toMonoidHom := by
  let f' : MulAut G := e⁻¹*f*e
  have hUVinv := map_aut_inverse U V e hUV
  have hVUinv := map_aut_inverse V U e hVU
  have hU' : U.map f'.toMonoidHom=U := by
    change U.map (e⁻¹*f*e).toMonoidHom=U
    rw [map_aut_mul,map_aut_mul,hUV,hV,hUVinv]
  have hV' : V.map f'.toMonoidHom=V := by
    change V.map (e⁻¹*f*e).toMonoidHom=V
    rw [map_aut_mul,map_aut_mul,hVU,hU,hVUinv]
  intro i
  have hN := hfix f' hU' hV' i
  have heq : f.toMonoidHom.comp e.toMonoidHom=e.toMonoidHom.comp f'.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change f (e x)=e (e.symm (f (e x)))
    exact (e.apply_symm_apply _).symm
  rw [Subgroup.map_map,heq,←Subgroup.map_map,hN]

theorem original_pair_fixer_fixes_signed_roots (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hU : (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map f.toMonoidHom=
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    (∀a:Bool,(originalPositiveOrbitRoot q a).map f.toMonoidHom=originalPositiveOrbitRoot q a) ∧
    (∀a:Bool,(originalNegativeOrbitRoot q a).map f.toMonoidHom=originalNegativeOrbitRoot q a) := by
  constructor
  · have hp := opposite_family_fix (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))
      (originalNegative q) (originalNegativeOrbitRoot q) (MulAut.conj (originalOpposition q))
      (original_positive_opposition_map q) (original_negative_opposition_map q)
      (fun F hFU hFV=>
        (original_pair_fixer_fixes_parabolics_and_negative_roots q F hFU hFV).2) f hU hV
    intro a
    simpa only [original_negative_axis_opposition_map] using hp a
  · exact (original_pair_fixer_fixes_parabolics_and_negative_roots q f hU hV).2

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedRootAction
