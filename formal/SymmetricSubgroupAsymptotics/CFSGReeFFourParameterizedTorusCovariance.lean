import SymmetricSubgroupAsymptotics.CFSGFFourOriginalParameterizedTorus
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance

/-! The actual exceptional involution transports parameterized original
F4 Weyl and torus words by the prescribed alpha/beta field maps. This is
word covariance, not yet a claim that a product torus is fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourParameterizedTorusCovariance
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalParameterizedTorus CFSGFFourOriginalMiddleWords
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourMiddleRootCovariance

private def parameterPower (m : ℕ) (i : Fin 4) : Field m→+*Field m :=
  if i.val<2 then alpha m else beta m

private theorem parameterPower_eq_power (m : ℕ) (i : Fin 4) (a : Field m) :
    parameterPower m i a=a^(originalExponent m i) := by
  rw [original_parameter_power]
  by_cases hi : i.val<2 <;> simp only [parameterPower,hi,if_true,if_false]

def unitPower (m : ℕ) (i : Fin 4) (a : (Field m)ˣ) : (Field m)ˣ :=
  Units.map (parameterPower m i).toMonoidHom a

theorem unitPower_val (m : ℕ) (i : Fin 4) (a : (Field m)ˣ) :
    (unitPower m i a : Field m)=(a : Field m)^(originalExponent m i) :=
  parameterPower_eq_power m i a

theorem ree_parameterWeyl (m : ℕ) (i : Fin 4) (a : (Field m)ˣ) :
    reeAutomorphism m (parameterWeyl (Field m) i a)=
      parameterWeyl (Field m) (CFSG.Models.reverseNode i) (unitPower m i a) := by
  have hroot (neg : Bool) (t : Field m) :
      reeAutomorphism m (modelRoot CartanMatrix.F₄ (Field m) neg i t)=
        modelRoot CartanMatrix.F₄ (Field m) neg (CFSG.Models.reverseNode i)
          (parameterPower m i t) := by
    rw [reeAutomorphism_root,parameterPower_eq_power]
  have ha : (unitPower m i a : Field m)=parameterPower m i (a : Field m) := rfl
  simp only [parameterWeyl,map_mul,hroot,ha,map_neg,map_inv₀]

theorem ree_parameterTorus (m : ℕ) (i : Fin 4) (a : (Field m)ˣ) :
    reeAutomorphism m (parameterTorus (Field m) i a)=
      parameterTorus (Field m) (CFSG.Models.reverseNode i) (unitPower m i a) := by
  simp only [parameterTorus,map_mul,map_inv,ree_parameterWeyl,ree_weyl]

end SymmetricSubgroupAsymptotics.CFSGReeFFourParameterizedTorusCovariance
