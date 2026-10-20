import SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniform
import SymmetricSubgroupAsymptotics.ModuleGeneratorTwoByFourMatrixUnits
import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Perm.Fin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinarySymmetricThreeFourColumnUniform
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev Bit := ZMod 2
abbrev Space := Fin 2 → Fin 4 → Bit
abbrev Top := Equiv.Perm (Fin 3)
def full (v : Space) : Fin 3 → Fin 4 → Bit := ![v 0,v 1,-v 0-v 1]
def operator (p : Top) : Module.End Bit Space where
  toFun v := fun i => full v (p⁻¹ i.castSucc)
  map_add' v w := by
    funext i j
    change full (v+w) (p⁻¹ i.castSucc) j=full v (p⁻¹ i.castSucc) j+full w (p⁻¹ i.castSucc) j
    generalize p⁻¹ i.castSucc=t
    fin_cases t <;> simp [full] <;> ring
  map_smul' z v := by
    funext i j
    change full (z • v) (p⁻¹ i.castSucc) j=z*full v (p⁻¹ i.castSucc) j
    generalize p⁻¹ i.castSucc=t
    fin_cases t <;> simp [full,mul_sub]
private theorem operator_one : operator 1=1 := by
  apply LinearMap.ext
  intro v
  funext i j
  fin_cases i <;> rfl
private def scalar (p : Top) (v : Fin 2 → Bit) (i : Fin 2) : Bit :=
  (![v 0,v 1,-v 0-v 1] : Fin 3 → Bit) (p⁻¹ i.castSucc)
private theorem scalar_mul : ∀ (p q : Top) (v : Fin 2 → Bit),
    scalar (p*q) v=scalar p (scalar q v) := by decide +kernel
private theorem operator_column (p : Top) (v : Space) (j : Fin 4) :
    (fun i => operator p v i j)=scalar p (fun i => v i j) := by
  funext i
  change full v (p⁻¹ i.castSucc) j=(![v 0 j,v 1 j,-v 0 j-v 1 j] : Fin 3 → Bit) (p⁻¹ i.castSucc)
  generalize p⁻¹ i.castSucc=t
  fin_cases t <;> rfl
private theorem operator_mul (p q : Top) : operator (p*q)=operator p*operator q := by
  apply LinearMap.ext
  intro v
  funext i j
  change operator (p*q) v i j=operator p (operator q v) i j
  calc
    operator (p*q) v i j=scalar (p*q) (fun r => v r j) i := congrFun (operator_column (p*q) v j) i
    _ = scalar p (scalar q (fun r => v r j)) i := congrFun (scalar_mul p q (fun r => v r j)) i
    _ = scalar p (fun r => operator q v r j) i := congrArg (fun w => scalar p w i) (operator_column q v j).symm
    _ = operator p (operator q v) i j := (congrFun (operator_column p (operator q v) j) i).symm
 def rho : Representation Bit Top Space where
  toFun := operator
  map_one' := operator_one
  map_mul' := operator_mul
private def matrixOperator (i j : Fin 2) : Module.End Bit Space :=
  let A := rho (finRotate 3)
  let B := rho (Equiv.swap 0 1)
  if i=0 then (if j=0 then A+B else (A+B)*B)
  else (if j=0 then B*(A+B) else 1+A+B)
private def scalarMatrix (i j : Fin 2) (v : Fin 2 → Bit) : Fin 2 → Bit :=
  let A := scalar (finRotate 3)
  let B := scalar (Equiv.swap 0 1)
  let D := fun v => A v+B v
  if i=0 then (if j=0 then D v else D (B v))
  else (if j=0 then B (D v) else v+D v)
private theorem scalar_matrix : ∀ (i j : Fin 2) (v : Fin 2 → Bit),
    scalarMatrix i j v=Pi.single i (v j) := by decide +kernel
private theorem matrix_apply (i j : Fin 2) (v : Space) :
    matrixOperator i j v=Pi.single i (v j) := by
  funext r t
  have h := congrFun (scalar_matrix i j (fun s => v s t)) r
  fin_cases i <;> fin_cases j <;> fin_cases r <;>
    simpa [scalarMatrix,matrixOperator,rho,operator,full,scalar,Pi.single_apply,add_assoc] using h
 theorem module_uniform (W : Submodule Bit[Top] rho.asModule) : ModuleGeneratedBy Bit[Top] W 2 := by
  let e : rho.asModule ≃ₗ[Bit] Space := rho.asModuleEquiv
  apply ModuleGeneratedBy.two_of_matrixUnits_two_by_four
    (k:=Bit) (R:=Bit[Top]) (M:=rho.asModule) e
    (BinarySymmetricThreeTwoRowUniform.matrixScalar (finRotate 3) (Equiv.swap 0 1)) ?_ W
  intro i j x
  change rho.asAlgebraHom (BinarySymmetricThreeTwoRowUniform.matrixScalar
    (finRotate 3) (Equiv.swap 0 1) i j) x=Pi.single i (x j)
  have hm : rho.asAlgebraHom (BinarySymmetricThreeTwoRowUniform.matrixScalar
      (finRotate 3) (Equiv.swap 0 1) i j)=matrixOperator i j := by
    fin_cases i <;> fin_cases j <;>
      simp [BinarySymmetricThreeTwoRowUniform.matrixScalar,matrixOperator]
  rw [hm]
  exact matrix_apply i j x
 theorem uniform_two : UniformSubrepresentationGeneratorBound rho 2 :=
  (uniformSubrepresentationGeneratorBound_iff_submodule rho 2).mpr module_uniform
end SymmetricSubgroupAsymptotics.BinarySymmetricThreeFourColumnUniform
