import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeCentralGraph
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-! The actual two-endpoint scalar commutator of the ordinary middle
complement, with the full three-coordinate centre retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCommutator
open scoped commutatorElement
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleCentralWords
open CFSGGTwoCharacteristicThreeCentralGraph
open CFSGGTwoOriginalPositiveCollecting CFSGGTwoOriginalPositiveRootWords
variable (K : Type) [Field K] [CharP K 3] [Finite K]

def highHom : Multiplicative K →* Middle K :=
  (centralHom K).comp (vertical K).toMultiplicative

theorem coordinates_highHom (a : Multiplicative K) :
    coordinates K (highHom K a) = ![0,0,0,0,a.toAdd] := by
  change coordinates K (word K ![0,0,0,0,a.toAdd]) = _
  exact coordinates_word K _

theorem highHom_injective : Function.Injective (highHom K) := by
  intro a b hab
  have he : Multiplicative.ofAdd (vertical K a.toAdd) =
      Multiplicative.ofAdd (vertical K b.toAdd) := centralHom_injective K hab
  exact congrArg (fun x : Multiplicative (Fin 3 → K) => x.toAdd 2) he

theorem highHom_val (a : Multiplicative K) :
    (highHom K a).val = positiveModel K 5 a.toAdd := by
  change (centralHom K (Multiplicative.ofAdd ![0,0,a.toAdd])).val = _
  rw [centralHom_val,centralWord_modelWord]
  change positiveModel K 0 0*positiveModel K 1 0*positiveModel K 2 0*
    positiveModel K 3 0*positiveModel K 4 0*positiveModel K 5 a.toAdd = _
  simp only [positiveModel_zero,one_mul]

private theorem commutator_of_twisted_mul {G : Type*} [Group G] (u v z : G)
    (h : u*v=z*v*u) : ⁅u,v⁆=z := by
  rw [commutatorElement_def,h]
  group

theorem commutator_eq (u v : Middle K) :
    ⁅u,v⁆ = highHom K (Multiplicative.ofAdd
      (coordinates K u 3*coordinates K v 0-coordinates K u 0*coordinates K v 3)) := by
  apply commutator_of_twisted_mul
  apply (coordinateEquiv K).symm.injective
  change coordinates K (u*v) = coordinates K
    (highHom K (Multiplicative.ofAdd
      (coordinates K u 3*coordinates K v 0-coordinates K u 0*coordinates K v 3))*v*u)
  simp only [coordinates_mul,coordinates_highHom]
  funext i
  fin_cases i <;> simp [multiplyCoordinates] <;> ring

theorem high_parameter_is_commutator (a : K) :
    ∃ u v : Middle K, ⁅u,v⁆ = highHom K (Multiplicative.ofAdd a) := by
  refine ⟨word K ![0,0,0,a,0],word K ![1,0,0,0,0],?_⟩
  rw [commutator_eq,coordinates_word,coordinates_word]
  apply congrArg (highHom K)
  apply congrArg Multiplicative.ofAdd
  change a*1-0*0=a
  ring

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCommutator
