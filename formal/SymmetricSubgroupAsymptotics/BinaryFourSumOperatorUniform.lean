import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import Mathlib.Algebra.Field.ZMod
set_option autoImplicit false
noncomputable section
open scoped BigOperators MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryFourSumOperatorUniform
abbrev Bit := ZMod 2
abbrev Space := Fin 4 → Bit
 def operator : Module.End Bit Space where
  toFun v := fun _ => ∑ i,v i
  map_add' v w := by ext i; simp [Finset.sum_add_distrib]
  map_smul' z v := by ext i; simp [Finset.mul_sum]
private def vector (j : Fin 3) (n : Fin 2) : Space :=
  if n=0 then Pi.single j.castSucc 1 else fun _ => 1
private def selected : Fin 4 → Fin 3 × Fin 2 := ![(0,0),(1,0),(2,0),(0,1)]
private def coefficient (i j : Fin 4) : Bit :=
  if i=3 then 1 else if i=j then 1 else 0
 def witness : LiteralPolynomialSpanWitness operator 3 1 where
  vectors := vector
  step := by decide +kernel
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel
 theorem uniform {H : Type} [Group H] (rho : Representation Bit H Space)
    (a : Bit[H]) (ha : operator=rho.asAlgebraHom a) :
    UniformSubrepresentationGeneratorBound rho 3 := witness.uniform rho a ha
end SymmetricSubgroupAsymptotics.BinaryFourSumOperatorUniform
