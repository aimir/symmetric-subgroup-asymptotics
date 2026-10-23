import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProductTorusParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters

/-! The actual original G2 product torus preserves both literal root
parts and every labelled signed simple chart. Its exact scalar action
is the unimodular folded Cartan map, with inverse scalars on negatives. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProductTorusAction
open CFSGGTwoD4GeckProductTorusParameters CFSGGTwoD4GeckRelativeProductTorus
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckSimpleParameters CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRelativeRootGenerated CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalProductTorus : (Fin 2→Kˣ)→*Projective CartanMatrix.G₂ K :=
  (generatedToOriginal K).comp (relativeProductTorus K)

theorem originalProductTorus_simple_action (x : Fin 2→Kˣ) (neg a : Bool) (t : K) :
    originalProductTorus K x*originalSimpleHom K neg a (Multiplicative.ofAdd t)*
      (originalProductTorus K x)⁻¹=
        originalSimpleHom K neg a (Multiplicative.ofAdd (t*(parameterScalar K x neg a : K))) := by
  have he := congrArg (generatedToOriginal K) (relativeProductTorus_simple_action K x neg a t)
  rw [map_mul (generatedToOriginal K),map_mul (generatedToOriginal K),map_inv (generatedToOriginal K)] at he
  exact he

theorem originalProductTorus_normalizes (x : Fin 2→Kˣ) (neg : Bool) :
    originalProductTorus K x∈Subgroup.normalizer
      ((rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K) :
        Set (Projective CartanMatrix.G₂ K)) :=
  Subgroup.le_normalizer_map (generatedToOriginal K)
    ⟨relativeProductTorus K x,relativeProductTorus_normalizes K x neg,rfl⟩

theorem originalProductTorus_simple_range (x : Fin 2→Kˣ) (neg a : Bool) :
    (originalSimpleHom K neg a).range.map (MulAut.conj (originalProductTorus K x)).toMonoidHom=
      (originalSimpleHom K neg a).range := by
  apply le_antisymm
  · rintro y ⟨u,⟨t,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd (t.toAdd*(parameterScalar K x neg a : K)),?_⟩
    change originalSimpleHom K neg a (Multiplicative.ofAdd (t.toAdd*(parameterScalar K x neg a : K)))=
      originalProductTorus K x*originalSimpleHom K neg a t*(originalProductTorus K x)⁻¹
    exact (originalProductTorus_simple_action K x neg a t.toAdd).symm
  · rintro y ⟨t,rfl⟩
    let b : Multiplicative K := Multiplicative.ofAdd (t.toAdd/(parameterScalar K x neg a : K))
    refine ⟨originalSimpleHom K neg a b,⟨b,rfl⟩,?_⟩
    change originalProductTorus K x*originalSimpleHom K neg a b*(originalProductTorus K x)⁻¹=
      originalSimpleHom K neg a t
    have he := originalProductTorus_simple_action K x neg a
      (t.toAdd/(parameterScalar K x neg a : K))
    rw [div_mul_cancel₀ t.toAdd (Units.ne_zero (parameterScalar K x neg a))] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProductTorusAction
