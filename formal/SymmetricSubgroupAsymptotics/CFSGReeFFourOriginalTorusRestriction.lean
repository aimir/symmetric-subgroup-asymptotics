import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterSemilinear
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleSemilinear

/-! Actual inner automorphisms from the original fixed torus belong to
its opposed-pair stabilizer, and their two positive restrictions are the
literal scalar and Suzuki-torus maps. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalTorusRestriction
open CFSGReeFFourFieldParameters CFSGReeFFourPerfectProjection
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourFixedTorus CFSGReeFFourFixedDiagonalCardinality
open CFSGReeFFourFixedOuterTorusAction CFSGReeFFourFixedMiddleTorusAction
open CFSGReeFFourOriginalOuterSemilinear CFSGReeFFourOriginalMiddleSemilinear
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourOuterTorusAction
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOriginalOppositeAlignment
open CFSGFiniteFieldScalarNormalizer

def torusPairAut (m : ℕ) (hm : 0<m) (u v : (Field m)ˣ) : pairStabilizer m hm :=
  ⟨MulAut.conj (fixedToOriginal m hm (fixedTorus m u v)),by
    have hd : fixedToOriginal m hm (fixedTorus m u v)∈originalDiagonal m hm := by
      rw [←fixedDiagonal_map_originalDiagonal m hm]
      exact ⟨fixedTorus m u v,fixedTorus_mem_diagonal m u v,rfl⟩
    intro neg
    cases neg
    · apply SetLike.coe_injective
      exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hd.1
    · apply SetLike.coe_injective
      exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hd.2⟩

theorem torusPairAut_val (m : ℕ) (hm : 0<m) (u v : (Field m)ˣ) :
    (torusPairAut m hm u v).val=MulAut.conj (fixedToOriginal m hm (fixedTorus m u v)) := rfl

theorem outerAction_torusPairAut (m : ℕ) (hm : 0<m) (u v : (Field m)ˣ) :
    outerAction m hm (torusPairAut m hm u v)=scalarHom (Field m) (outerScalar m u v) := by
  apply AddEquiv.ext
  intro x
  have he := outerRestriction_intertwines m hm (torusPairAut m hm u v) x
  change originalOuterHom m hm (Multiplicative.ofAdd (outerAction m hm (torusPairAut m hm u v) x))=
    fixedToOriginal m hm (fixedTorus m u v)*originalOuterHom m hm (Multiplicative.ofAdd x)*
      (fixedToOriginal m hm (fixedTorus m u v))⁻¹ at he
  rw [original_fixed_torus_outer_action] at he
  have hp := congrArg Multiplicative.toAdd (originalOuterHom_injective m hm he)
  change outerAction m hm (torusPairAut m hm u v) x=x*(outerScalar m u v : Field m) at hp
  exact hp.trans (mul_comm _ _)

theorem middleAction_torusPairAut (m : ℕ) (hm : 0<m) (u v : (Field m)ˣ) :
    middleAction m hm (torusPairAut m hm u v)=
      CFSGSuzukiUnipotent.torusAutHom m (middleScalar m u v)⁻¹ := by
  apply MulEquiv.ext
  intro x
  apply originalMiddleEmbedding_injective m hm
  have he := middleRestriction_embedding m hm (torusPairAut m hm u v) x
  change originalMiddleEmbedding m hm (middleAction m hm (torusPairAut m hm u v) x)=
    fixedToOriginal m hm (fixedTorus m u v)*originalMiddleEmbedding m hm x*
      (fixedToOriginal m hm (fixedTorus m u v))⁻¹ at he
  exact he.trans (original_fixed_torus_middle_action m hm u v x).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalTorusRestriction
