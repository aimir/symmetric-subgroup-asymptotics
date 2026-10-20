import SymmetricSubgroupAsymptotics.BinaryFourSumOperatorUniform
import SymmetricSubgroupAsymptotics.BinaryJordanPlusTrivialUniformGenerators
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryFourSumCornerRepresentation
open BinaryFourSumOperatorUniform (Bit Space operator)
abbrev Binary := Multiplicative (ZMod 2)
 def reflection : Space ≃ₗ[Bit] Space where
  toFun := (1+operator : Module.End Bit Space)
  invFun := (1+operator : Module.End Bit Space)
  left_inv := by
    have h : ∀ v : Space,(1+operator : Module.End Bit Space) ((1+operator : Module.End Bit Space) v)=v := by decide +kernel
    exact h
  right_inv := by
    have h : ∀ v : Space,(1+operator : Module.End Bit Space) ((1+operator : Module.End Bit Space) v)=v := by decide +kernel
    exact h
  map_add' := (1+operator : Module.End Bit Space).map_add
  map_smul' := (1+operator : Module.End Bit Space).map_smul
 theorem reflection_square : reflection^2=1 := by
  apply LinearEquiv.ext
  intro v
  have h : ∀ v : Space,(reflection^2) v=v := by decide +kernel
  exact h v
 def linear : Binary →* (Space ≃ₗ[Bit] Space) := BinaryFourBlockAugmentation.powersHom 2 reflection reflection_square
 def rho : Representation Bit Binary Space := LinearSemidirectCoprimeSocleBounds.linearRepresentation linear
 theorem operator_eq : operator=rho.asAlgebraHom
    (MonoidAlgebra.single (Multiplicative.ofAdd 1 : Binary) 1+1) := by
  simp only [map_add,map_one,Representation.asAlgebraHom_single_one]
  have hr : rho (Multiplicative.ofAdd 1)=1+operator := by
    change (reflection^1).toLinearMap=1+operator
    rw [pow_one]
    rfl
  rw [hr]
  apply LinearMap.ext
  intro v
  funext i
  change operator v i=(v i+operator v i)+v i
  ring_nf
  norm_num
  exact Or.inr (show (2 : ZMod 2)=0 by decide +kernel)
 theorem uniform_three : UniformSubrepresentationGeneratorBound rho 3 :=
  BinaryFourSumOperatorUniform.uniform rho _ operator_eq
end SymmetricSubgroupAsymptotics.BinaryFourSumCornerRepresentation
