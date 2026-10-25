import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveCoordinateKernels

/-! Five-coordinate words cover the literal ordinary simple complement
in every characteristic-three field, including the field with three
elements. Their law is inherited from actual six-word collection; no
cubic-curve spanning or abstract radical recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
open CFSG.Models.Chevalley CFSGGTwoPositiveSixWord
open CFSGGTwoPositiveCoordinateKernels CFSGGTwoPositiveWordMultiplication
variable (K : Type) [Field K] [CharP K 3]

def extendCoordinates (v : Fin 5 → K) : Fin 6 → K := ![0,v 0,v 1,v 2,v 3,v 4]

def middleWord (v : Fin 5 → K) : Model CartanMatrix.G₂ K := modelWord K (extendCoordinates K v)

def multiplyCoordinates (v w : Fin 5 → K) : Fin 5 → K :=
  ![v 0+w 0,v 1+w 1,v 2+w 2,v 3+w 3,v 4+w 4+w 0*v 3]

theorem middleWord_injective : Function.Injective (middleWord K) := by
  intro v w he
  have h := modelWord_injective K he
  funext i
  fin_cases i
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5

theorem middleWord_mem_complement (v : Fin 5 → K) : middleWord K v ∈ complement K 0 :=
  (mem_complement_iff K 0 _).mpr ⟨extendCoordinates K v,rfl,rfl⟩

theorem mem_complement_iff_middleWord (g : Model CartanMatrix.G₂ K) :
    g ∈ complement K 0 ↔ ∃ v : Fin 5 → K, middleWord K v = g := by
  constructor
  · intro hg
    obtain ⟨x,hx,hzero⟩ := (mem_complement_iff K 0 g).mp hg
    have hx0 : x 0 = 0 := hzero
    let v : Fin 5 → K := ![x 1,x 2,x 3,x 4,x 5]
    refine ⟨v,?_⟩
    have he : extendCoordinates K v = x := by
      funext i
      fin_cases i
      · exact hx0.symm
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    change modelWord K (extendCoordinates K v) = g
    rw [he]
    exact hx
  · rintro ⟨v,rfl⟩
    exact middleWord_mem_complement K v

theorem middleWord_mul (v w : Fin 5 → K) :
    middleWord K v*middleWord K w = middleWord K (multiplyCoordinates K v w) := by
  change modelWord K (extendCoordinates K v)*modelWord K (extendCoordinates K w) = _
  rw [modelWord_mul]
  apply congrArg (modelWord K)
  funext i
  fin_cases i <;> simp [productCoordinates,extendCoordinates,multiplyCoordinates]

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
