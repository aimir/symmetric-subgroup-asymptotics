import SymmetricSubgroupAsymptotics.CFSGTrialityD4NormTwo
import SymmetricSubgroupAsymptotics.CFSGGeckSerreRepresentation
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-! Literal G2 folded generators in the SAME D4 Geck matrices.
Node zero is the sum of the three outer nodes and node one is central.
The actual four bracket relations use the original G2 Cartan matrix.
No identification of matrix groups or quotient faithfulness is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGenerators
open CFSGTrialityD4NormTwo CFSGNormTwoRootPairing

abbrev GeckIndex := Base.support⊕Roots (CartanMatrix.D 4)
abbrev Mat := Matrix GeckIndex GeckIndex ℚ

def d4H (i : Fin 4) : Mat := CFSGGeckSerreRepresentation.H Base Index i
def d4E (i : Fin 4) : Mat := CFSGGeckSerreRepresentation.E Base Index i
def d4F (i : Fin 4) : Mat := CFSGGeckSerreRepresentation.F Base Index i

theorem d4HH (i j : Fin 4) : ⁅d4H i,d4H j⁆=0 :=
  CFSGGeckSerreRepresentation.HH Base Index i j

theorem d4EF (i j : Fin 4) : ⁅d4E i,d4F j⁆=if i=j then d4H i else 0 :=
  CFSGGeckSerreRepresentation.EF Base Index i j

theorem d4HE (i j : Fin 4) : ⁅d4H i,d4E j⁆=CartanMatrix.D 4 i j • d4E j := by
  simpa only [d4H,d4E,cartan_eq] using CFSGGeckSerreRepresentation.HE Base Index i j

theorem d4HF (i j : Fin 4) : ⁅d4H i,d4F j⁆= -(CartanMatrix.D 4 i j • d4F j) := by
  simpa only [d4H,d4F,cartan_eq] using CFSGGeckSerreRepresentation.HF Base Index i j

def cartan (i : Fin 2) : Mat := ![d4H 0+d4H 2+d4H 3,d4H 1] i
def positive (i : Fin 2) : Mat := ![d4E 0+d4E 2+d4E 3,d4E 1] i
def negative (i : Fin 2) : Mat := ![d4F 0+d4F 2+d4F 3,d4F 1] i
def representative (i : Fin 2) : Fin 4 := ![0,1] i

theorem HH (i j : Fin 2) : ⁅cartan i,cartan j⁆=0 := by
  fin_cases i <;> fin_cases j <;> simp [cartan,add_lie,lie_add,d4HH]

theorem EF (i j : Fin 2) : ⁅positive i,negative j⁆=if i=j then cartan i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [positive,negative,cartan,add_lie,lie_add,d4EF]

theorem HE (i j : Fin 2) : ⁅cartan i,positive j⁆=CartanMatrix.G₂ i j • positive j := by
  fin_cases i <;> fin_cases j
  · change ⁅d4H 0+d4H 2+d4H 3,d4E 0+d4E 2+d4E 3⁆=
      (2:ℤ) • (d4E 0+d4E 2+d4E 3)
    simp only [add_lie,lie_add,d4HE]
    norm_num [CartanMatrix.D,Fin.ext_iff] <;> module
  · change ⁅d4H 0+d4H 2+d4H 3,d4E 1⁆=(-3:ℤ) • d4E 1
    simp only [add_lie,d4HE]
    rw [show CartanMatrix.D 4 (0:Fin 4) 1=(-1:ℤ) by decide,
      show CartanMatrix.D 4 (2:Fin 4) 1=(-1:ℤ) by decide,
      show CartanMatrix.D 4 (3:Fin 4) 1=(-1:ℤ) by decide,
      ←add_smul,←add_smul]
    norm_num
  · change ⁅d4H 1,d4E 0+d4E 2+d4E 3⁆=(-1:ℤ) • (d4E 0+d4E 2+d4E 3)
    simp only [lie_add,d4HE]
    norm_num [CartanMatrix.D,Fin.ext_iff] <;> module
  · change ⁅d4H 1,d4E 1⁆=(2:ℤ) • d4E 1
    simpa only [show CartanMatrix.D 4 (1:Fin 4) 1=(2:ℤ) by decide] using d4HE 1 1

theorem HF (i j : Fin 2) : ⁅cartan i,negative j⁆= -(CartanMatrix.G₂ i j • negative j) := by
  fin_cases i <;> fin_cases j
  · change ⁅d4H 0+d4H 2+d4H 3,d4F 0+d4F 2+d4F 3⁆=
      -((2:ℤ) • (d4F 0+d4F 2+d4F 3))
    simp only [add_lie,lie_add,d4HF]
    norm_num [CartanMatrix.D,Fin.ext_iff] <;> module
  · change ⁅d4H 0+d4H 2+d4H 3,d4F 1⁆= -((-3:ℤ) • d4F 1)
    simp only [add_lie,d4HF]
    rw [show CartanMatrix.D 4 (0:Fin 4) 1=(-1:ℤ) by decide,
      show CartanMatrix.D 4 (2:Fin 4) 1=(-1:ℤ) by decide,
      show CartanMatrix.D 4 (3:Fin 4) 1=(-1:ℤ) by decide,
      ←neg_add,←neg_add,←add_smul,←add_smul]
    norm_num
  · change ⁅d4H 1,d4F 0+d4F 2+d4F 3⁆= -((-1:ℤ) • (d4F 0+d4F 2+d4F 3))
    simp only [lie_add,d4HF]
    norm_num [CartanMatrix.D,Fin.ext_iff] <;> module
  · change ⁅d4H 1,d4F 1⁆= -((2:ℤ) • d4F 1)
    simpa only [show CartanMatrix.D 4 (1:Fin 4) 1=(2:ℤ) by decide] using d4HF 1 1

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGenerators
