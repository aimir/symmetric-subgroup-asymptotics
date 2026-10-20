import SymmetricSubgroupAsymptotics.ModuleGeneratorMatrixUnits
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniform
abbrev Bit := ZMod 2
abbrev Space := Fin 2 → Fin 2 → Bit

def cycle : Module.End Bit Space where
  toFun v := ![v 0+v 1,v 0]
  map_add' _ _ := by ext i j; fin_cases i <;> simp <;> abel
  map_smul' _ _ := by ext i j; fin_cases i <;> simp [mul_add]
def swap : Module.End Bit Space where
  toFun v := ![v 1,v 0]
  map_add' _ _ := by ext i j; fin_cases i <;> simp
  map_smul' _ _ := by ext i j; fin_cases i <;> simp
private def matrixOperator (i j : Fin 2) : Module.End Bit Space :=
  if i=0 then (if j=0 then cycle+swap else (cycle+swap)*swap)
  else (if j=0 then swap*(cycle+swap) else 1+cycle+swap)
private theorem matrixOperator_apply : ∀ (i j : Fin 2) (v : Space),
    matrixOperator i j v=Pi.single i (v j) := by
  decide +kernel

def matrixScalar {H : Type} [Group H] (a b : H) (i j : Fin 2) : Bit[H] :=
  let A := MonoidAlgebra.single a 1
  let B := MonoidAlgebra.single b 1
  if i=0 then (if j=0 then A+B else (A+B)*B)
  else (if j=0 then B*(A+B) else 1+A+B)

theorem module_uniform {H : Type} [Group H]
    (rho : Representation Bit H Space) (a b : H)
    (ha : rho a=cycle) (hb : rho b=swap)
    (W : Submodule Bit[H] rho.asModule) : ModuleGeneratedBy Bit[H] W 1 := by
  let e : rho.asModule ≃ₗ[Bit] Space := rho.asModuleEquiv
  apply ModuleGeneratedBy.one_of_matrixUnits (by decide : 2≤2) e (matrixScalar a b) ?_ W
  intro i j x
  change rho.asAlgebraHom (matrixScalar a b i j) x=Pi.single i (x j)
  have hm : rho.asAlgebraHom (matrixScalar a b i j)=matrixOperator i j := by
    fin_cases i <;> fin_cases j <;>
      simp [matrixScalar,matrixOperator,map_add,map_mul,Representation.asAlgebraHom_single_one,ha,hb]
  rw [hm]
  exact matrixOperator_apply i j x
end SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniform
