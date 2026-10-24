import SymmetricSubgroupAsymptotics.CFSGFFourOriginalTorusCommutation
import SymmetricSubgroupAsymptotics.CFSGReeFFourParameterizedTorusCovariance
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedModelEquivalence

/-! Genuine two-unit torus words in the same original exceptional-fixed
group. Fixedness follows from the actual signed-root covariance and
proved simple-torus commutation, not from scalar arithmetic alone. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorus
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourParameterizedTorusCovariance
open CFSGFFourOriginalProductTorus CFSGFFourOriginalParameterizedTorus
open CFSGFFourOriginalTorusCommutation

theorem unitPower_reverse (m : ℕ) (i : Fin 4) (a : (Field m)ˣ) :
    unitPower m (CFSG.Models.reverseNode i) (unitPower m i a)=a := by
  apply Units.ext
  rw [unitPower_val,unitPower_val]
  exact original_parameter_power_twice m i a

def fixedTorusTuple (m : ℕ) (a b : (Field m)ˣ) : Fin 4→(Field m)ˣ :=
  ![a,b,unitPower m 1 b,unitPower m 0 a]

private theorem tuple_zero (m : ℕ) (a b : (Field m)ˣ) : fixedTorusTuple m a b 0=a := rfl
private theorem tuple_one (m : ℕ) (a b : (Field m)ˣ) : fixedTorusTuple m a b 1=b := rfl
private theorem tuple_two (m : ℕ) (a b : (Field m)ˣ) :
    fixedTorusTuple m a b 2=unitPower m 1 b := rfl
private theorem tuple_three (m : ℕ) (a b : (Field m)ˣ) :
    fixedTorusTuple m a b 3=unitPower m 0 a := rfl

theorem fixedTorusWord_fixed (m : ℕ) (a b : (Field m)ˣ) :
    reeAutomorphism m (modelProductTorusHom (Field m) (fixedTorusTuple m a b))=
      modelProductTorusHom (Field m) (fixedTorusTuple m a b) := by
  simp only [modelProductTorus_word]
  simp only [map_mul,ree_parameterTorus,tuple_zero,tuple_one,tuple_two,tuple_three]
  change parameterTorus (Field m) 3 (unitPower m 0 a)*
      (parameterTorus (Field m) 2 (unitPower m 1 b)*
        (parameterTorus (Field m) 0 (unitPower m (CFSG.Models.reverseNode 0) (unitPower m 0 a))*
          parameterTorus (Field m) 1 (unitPower m (CFSG.Models.reverseNode 1) (unitPower m 1 b))))=
    parameterTorus (Field m) 0 a*(parameterTorus (Field m) 1 b*
      (parameterTorus (Field m) 3 (unitPower m 0 a)*parameterTorus (Field m) 2 (unitPower m 1 b)))
  rw [unitPower_reverse,unitPower_reverse]
  have hZ := (parameterTorus_commute (Field m) 3 0 (unitPower m 0 a) a).mul_right
    (parameterTorus_commute (Field m) 3 1 (unitPower m 0 a) b)
  have hW := (parameterTorus_commute (Field m) 2 0 (unitPower m 1 b) a).mul_right
    (parameterTorus_commute (Field m) 2 1 (unitPower m 1 b) b)
  simpa only [mul_assoc] using (hZ.mul_left hW).eq

def fixedTorus (m : ℕ) (a b : (Field m)ˣ) : originalModelFixed m :=
  ⟨modelProductTorusHom (Field m) (fixedTorusTuple m a b),fixedTorusWord_fixed m a b⟩

theorem fixedTorus_val (m : ℕ) (a b : (Field m)ˣ) :
    (fixedTorus m a b).val=modelProductTorusHom (Field m) (fixedTorusTuple m a b) := rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorus
