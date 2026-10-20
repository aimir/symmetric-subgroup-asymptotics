import SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniformTransport
import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySymmetricThreeAugmentation
open BinarySymmetricThreeTwoRowUniform (Bit Space)
abbrev Top := Equiv.Perm (Fin 3)
def full (v : Space) : Fin 3 → Fin 2 → Bit := ![v 0,v 1,-v 0-v 1]
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
    fin_cases t <;> simp [full,mul_sub,mul_neg] <;> ring
private theorem operator_one : operator 1=1 := by
  apply LinearMap.ext
  intro v
  funext i j
  fin_cases i <;> rfl
private theorem operator_mul : ∀ p q : Top,operator (p*q)=operator p*operator q := by
  intro p q
  apply LinearMap.ext
  intro v
  have h : ∀ (p q : Top) (v : Space),operator (p*q) v=(operator p*operator q) v := by
    decide +kernel
  exact h p q v
 def rho : Representation Bit Top Space where
  toFun := operator
  map_one' := operator_one
  map_mul' := operator_mul
 theorem cycle_action : rho (finRotate 3)=BinarySymmetricThreeTwoRowUniform.cycle := by
  apply LinearMap.ext
  intro v
  have h : ∀ v : Space,rho (finRotate 3) v=BinarySymmetricThreeTwoRowUniform.cycle v := by decide +kernel
  exact h v
 theorem swap_action : rho (Equiv.swap 0 1)=BinarySymmetricThreeTwoRowUniform.swap := by
  apply LinearMap.ext
  intro v
  have h : ∀ v : Space,rho (Equiv.swap 0 1) v=BinarySymmetricThreeTwoRowUniform.swap v := by decide +kernel
  exact h v
 theorem uniform_one : UniformSubrepresentationGeneratorBound rho 1 :=
  BinarySymmetricThreeTwoRowUniform.uniform rho (finRotate 3) (Equiv.swap 0 1)
    cycle_action swap_action
 theorem fixed_free (v : Space) (h : ∀ o : alternatingGroup (Fin 3),rho o.val v=v) : v=0 := by
  have hc : finRotate 3 ∈ alternatingGroup (Fin 3) := by
    change Equiv.Perm.sign (finRotate 3)=1
    decide +kernel
  have hv := h ⟨finRotate 3,hc⟩
  have hz : ∀ w : Space,rho (finRotate 3) w=w → w=0 := by decide +kernel
  exact hz v hv
end SymmetricSubgroupAsymptotics.BinarySymmetricThreeAugmentation
