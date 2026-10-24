import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionFixedPositiveNegative

/-! Whole negative-preimage stability in the original Model follows from
whole positive stability and the actual fixed opposition word. This is
not a statement that the opposition belongs to the derived subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeStability
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalAmbientHom CFSGReeFFourAmbientPositiveStability
open CFSGReeFFourRelativeOpposition CFSGReeFFourOppositionFixedPositiveNegative
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckNormalizerEnvelope
open CFSGConjugateComap

private theorem hom_conjugation_comp {G : Type*} [Group G] (f : G→*G)
    (g : G) (hg : f g=g) :
    f.comp (MulAut.conj g).toMonoidHom=(MulAut.conj g).toMonoidHom.comp f := by
  apply MonoidHom.ext
  intro x
  change f (g*x*g⁻¹)=g*f x*g⁻¹
  rw [map_mul,map_mul,map_inv,hg]

def modelNegative (m : ℕ) : Subgroup (Model CartanMatrix.F₄ (Field m)) :=
  (Negative (Field m)).comap (rawHom (Field m))

theorem model_positive_image_eq_negative (m : ℕ) :
    (modelPositive (Field m)).map (MulAut.conj (relativeOpposition m)).toMonoidHom=modelNegative m := by
  have hraw : (Positive (Field m)).map
      (MulAut.conj (rawHom (Field m) (relativeOpposition m))).toMonoidHom=Negative (Field m) := by
    rw [rawHom_relativeOpposition]
    exact ambient_positive_image_eq_negative (Field m)
  change ((Positive (Field m)).comap (rawHom (Field m))).map
    (MulAut.conj (relativeOpposition m)).toMonoidHom=
      (Negative (Field m)).comap (rawHom (Field m))
  exact (comap_conjugate (rawHom (Field m)) (Positive (Field m)) (relativeOpposition m)).symm.trans
    (congrArg (fun S=>S.comap (rawHom (Field m))) hraw)

theorem ree_preserves_modelNegative (m : ℕ) :
    (modelNegative m).map (reeAutomorphism m).toMonoidHom=modelNegative m := by
  have hc : (reeAutomorphism m).toMonoidHom.comp
      (MulAut.conj (relativeOpposition m)).toMonoidHom=
    (MulAut.conj (relativeOpposition m)).toMonoidHom.comp (reeAutomorphism m).toMonoidHom := by
    exact hom_conjugation_comp (reeAutomorphism m).toMonoidHom (relativeOpposition m)
      (relativeOpposition_fixed m)
  rw [←model_positive_image_eq_negative,Subgroup.map_map,hc,←Subgroup.map_map,
    ree_preserves_modelPositive]

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeStability
