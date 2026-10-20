import SymmetricSubgroupAsymptotics.FunctionBlockOrbitUniform
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Field.ZMod
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryThreeBlockSignShearUniform
abbrev Bit := ZMod 2
abbrev Plane := Fin 2 → Bit
abbrev Space := Fin 3 → Plane
abbrev Top := Equiv.Perm (Fin 3)
def shear : Module.End Bit Plane where
  toFun v := ![v 0,v 0+v 1]
  map_add' _ _ := by ext i; fin_cases i <;> simp <;> abel
  map_smul' _ _ := by ext i; fin_cases i <;> simp [mul_add]
def operator (p : Top) : Module.End Bit Space where
  toFun v := fun i => if Equiv.Perm.sign p=1 then v (p⁻¹ i) else shear (v (p⁻¹ i))
  map_add' v w := by ext i j; by_cases h : Equiv.Perm.sign p=1 <;> simp [h,map_add]
  map_smul' z v := by ext i j; by_cases h : Equiv.Perm.sign p=1 <;> simp [h,map_smul]
private theorem operator_mul (p q : Top) : operator (p*q)=operator p*operator q := by
  apply LinearMap.ext
  intro v
  have h : ∀ (p q : Top) (v : Space),operator (p*q) v=(operator p*operator q) v := by decide +kernel
  exact h p q v
 def rho : Representation Bit Top Space where
  toFun := operator
  map_one' := by ext v i j; simp [operator]
  map_mul' := operator_mul
 theorem uniform_two : UniformSubrepresentationGeneratorBound rho 2 := by
  apply FunctionBlockOrbitUniform.uniform rho (finRotate 3) (0 : Fin 3) (Pi.basisFun Bit (Fin 2))
  intro i
  have h : ∀ i : Fin 3,∃ n : Fin 3,∀ v : Plane,
      rho ((finRotate 3)^n.val) (Pi.single 0 v)=Pi.single i v := by decide +kernel
  obtain ⟨n,hn⟩ := h i
  exact ⟨n.val,LinearEquiv.refl Bit Plane,hn⟩
end SymmetricSubgroupAsymptotics.BinaryThreeBlockSignShearUniform
