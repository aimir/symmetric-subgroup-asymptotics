import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeTorus

/-! Parameterized Weyl and torus words in the same original F4 Model.
Their literal raw values agree with the existing folded-generated words.
No simplicity of the ordinary projective F4 group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalParameterizedTorus
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourE6RelativeTorus
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6RelativeWords
open CFSGFFourE6FixedGeneratedGroup CFSGSerreQuadraticMatrix
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def parameterWeyl (i : Fin 4) (a : Kˣ) : Model CartanMatrix.F₄ K :=
  modelRoot CartanMatrix.F₄ K false i (a : K)*
    modelRoot CartanMatrix.F₄ K true i (-(a : K)⁻¹)*
      modelRoot CartanMatrix.F₄ K false i (a : K)

def parameterTorus (i : Fin 4) (a : Kˣ) : Model CartanMatrix.F₄ K :=
  parameterWeyl K i a*(weyl K i)⁻¹

private theorem raw_root_generated (neg : Bool) (i : Fin 4) (a : K) :
    rawHom K (modelRoot CartanMatrix.F₄ K neg i a)=
      (simpleInGenerated K neg i (Multiplicative.ofAdd a)).val := by
  rw [rawHom_root,simpleInGenerated_val,folded_root_eq_orbitParameter]
  fin_cases i <;> rfl

private theorem raw_weyl_generated (i : Fin 4) :
    rawHom K (weyl K i)=(simpleWeylInGenerated K i).val := by
  rw [rawHom_weyl,simpleWeylInGenerated_val]
  exact foldedWeyl_eq_orbitWord K i

theorem rawHom_parameterWeyl (i : Fin 4) (a : Kˣ) :
    rawHom K (parameterWeyl K i a)=(scaledWeylInGenerated K i a).val := by
  simp only [parameterWeyl,map_mul (rawHom K),raw_root_generated,
    scaledWeylInGenerated,Subgroup.coe_mul]

theorem rawHom_parameterTorus (i : Fin 4) (a : Kˣ) :
    rawHom K (parameterTorus K i a)=(torusInGenerated K i a).val := by
  simp only [parameterTorus,map_mul (rawHom K),map_inv (rawHom K),rawHom_parameterWeyl,
    raw_weyl_generated,torusInGenerated,Subgroup.coe_mul,Subgroup.coe_inv]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalParameterizedTorus
