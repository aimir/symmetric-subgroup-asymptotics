import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedMiddleTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusFirstLayer

/-! The actual Suzuki-coordinate middle group embeds in the SAME
original Ree quotient. All genuine fixed-torus actions on it are the
literal native Suzuki torus actions with the proved inverse scalar. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleTorusAction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourMiddleFixedWords
open CFSGReeFFourOriginalRootCoordinates CFSGReeFFourOriginalRootIntersections
open CFSGReeFFourMiddleSuzukiCoordinates CFSGReeFFourPerfectProjection

def originalMiddleEmbedding (m : ℕ) (hm : 0<m) :
    CFSGSuzukiUnipotent.unipotentSubgroup m →* CFSG.Models.ReeF4 m :=
  (originalRootBlock m hm true).subtype.comp (originalMiddleSuzukiEquiv m hm).symm.toMonoidHom

theorem originalMiddleEmbedding_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (originalMiddleEmbedding m hm) :=
  Subtype.val_injective.comp (originalMiddleSuzukiEquiv m hm).symm.injective

theorem originalMiddleEmbedding_coordinate (m : ℕ) (hm : 0<m) (a c : Field m) :
    originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m a c)=
      fixedToOriginal m hm (fixedMiddleParameter m (a,c)) := by
  have he : (originalMiddleSuzukiEquiv m hm).symm (CFSGSuzukiUnipotent.coordinateElement m a c)=
      middleOriginalEquiv m hm (middleCoordinateElement m a c) :=
    (originalMiddleSuzukiEquiv m hm).symm_apply_eq.mpr
      (originalMiddleSuzukiEquiv_coordinate m hm a c).symm
  have hv := congrArg (fun g : originalRootBlock m hm true=>g.val) he
  change originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m a c)=
    (middleOriginalEquiv m hm (middleCoordinateElement m a c)).val at hv
  exact hv.trans (middleOriginalEquiv_val m hm _)

theorem fixed_torus_middle_parameter_action (m : ℕ) (u v : (Field m)ˣ) (a c : Field m) :
    fixedTorus m u v*fixedMiddleParameter m (a,c)*(fixedTorus m u v)⁻¹=
      fixedMiddleParameter m (a*(middleScalar m u v : Field m),
        c*((middleScalar m u v : Field m)*alpha m (middleScalar m u v : Field m))) :=
  Subtype.ext (fixed_torus_middleWord_action m u v a c)

private theorem torus_inverse_coordinate (m : ℕ) (s : (Field m)ˣ) (a c : Field m) :
    CFSGSuzukiUnipotent.torusAutHom m s⁻¹ (CFSGSuzukiUnipotent.coordinateElement m a c)=
      CFSGSuzukiUnipotent.coordinateElement m (a*(s : Field m))
        (c*((s : Field m)*alpha m (s : Field m))) := by
  change CFSGSuzukiUnipotent.torusAction m s⁻¹ (CFSGSuzukiUnipotent.coordinateElement m a c)=_
  rw [CFSGSuzukiUnipotent.torusAction_coordinateElement]
  rw [←alpha_eq_suzukiTheta]
  congr 1 <;> simp only [Units.val_inv_eq_inv_val,map_inv₀,mul_inv_rev,inv_inv] <;> ring

theorem original_fixed_torus_middle_action (m : ℕ) (hm : 0<m)
    (u v : (Field m)ˣ) (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    originalMiddleEmbedding m hm
      (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m u v)⁻¹ x)=
      fixedToOriginal m hm (fixedTorus m u v)*originalMiddleEmbedding m hm x*
        (fixedToOriginal m hm (fixedTorus m u v))⁻¹ := by
  obtain ⟨⟨a,c⟩,rfl⟩ := (CFSGSuzukiUnipotent.parameterEquiv m).surjective x
  change originalMiddleEmbedding m hm
      (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m u v)⁻¹
        (CFSGSuzukiUnipotent.coordinateElement m a c))=
    fixedToOriginal m hm (fixedTorus m u v)*
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m a c)*
      (fixedToOriginal m hm (fixedTorus m u v))⁻¹
  rw [torus_inverse_coordinate,originalMiddleEmbedding_coordinate,originalMiddleEmbedding_coordinate]
  simpa only [map_mul,map_inv] using congrArg (fixedToOriginal m hm)
    (fixed_torus_middle_parameter_action m u v a c).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleTorusAction
