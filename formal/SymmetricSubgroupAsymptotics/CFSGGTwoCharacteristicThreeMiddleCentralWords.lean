import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherCollecting
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleWeylTransport

/-! Three literal central-word candidates for the five-coordinate
ordinary middle complement in characteristic three. Their injectivity
and signed torus/Weyl actions retain the SAME original Model. The full
centre identification and small-orbit graph argument remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralWords
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoPositiveSixWord CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoOriginalHigherCollecting CFSGGTwoOriginalSimpleWeylTransport
open CFSGGTwoOriginalPositiveTorusAction CFSGGTwoOriginalRankTwoTorus
open CFSGGTwoNaturalPositiveTorusAction
variable (K : Type) [Field K] [CharP K 3]

def centralCoordinates (v : Fin 3 → K) : Fin 4 → K := ![v 0,v 1,0,v 2]

def centralWord (v : Fin 3 → K) : Model CartanMatrix.G₂ K :=
  higherWord K (centralCoordinates K v)

theorem centralWord_modelWord (v : Fin 3 → K) :
    centralWord K v = modelWord K ![0,0,v 0,v 1,0,v 2] := by
  change positiveModel K 2 (v 0)*positiveModel K 3 (v 1)*positiveModel K 4 0*
      positiveModel K 5 (v 2) =
    positiveModel K 0 0*positiveModel K 1 0*positiveModel K 2 (v 0)*
      positiveModel K 3 (v 1)*positiveModel K 4 0*positiveModel K 5 (v 2)
  simp only [positiveModel_zero,one_mul,mul_one]

theorem centralWord_injective : Function.Injective (centralWord K) := by
  intro v w he
  rw [centralWord_modelWord,centralWord_modelWord] at he
  have h := modelWord_injective K he
  funext i
  fin_cases i
  · exact congrFun h 2
  · exact congrFun h 3
  · exact congrFun h 5

theorem centralWord_add (v w : Fin 3 → K) :
    centralWord K v*centralWord K w = centralWord K (v+w) := by
  change higherWord K (centralCoordinates K v)*higherWord K (centralCoordinates K w) = _
  rw [higherWord_add]
  apply congrArg (higherWord K)
  funext i
  fin_cases i <;> simp [centralCoordinates]

theorem centralWord_short_collect (v : Fin 3 → K) (a : K) :
    centralWord K v*positiveModel K 0 a =
      positiveModel K 0 a*centralWord K ![v 0,v 1-a*v 0,v 2] := by
  exact higherWord_short K (centralCoordinates K v) a

theorem torus_flip_centralWord (v : Fin 3 → K) :
    torusPair K (-1,1)*centralWord K v*(torusPair K (-1,1))⁻¹ =
      centralWord K ![-v 0,-v 1,v 2] := by
  rw [centralWord_modelWord,torusPair_modelWord,centralWord_modelWord]
  apply congrArg (modelWord K)
  funext i
  fin_cases i <;> simp [scaleCoordinates,rootScale]

theorem shortWeyl_centralWord (v : Fin 3 → K) :
    shortWord K*centralWord K v*(shortWord K)⁻¹ = centralWord K ![-v 1,v 0,v 2] := by
  let c : MulAut (Model CartanMatrix.G₂ K) := MulAut.conj (shortWord K)
  have hc (j : Fin 6) (a : K) : c (positiveModel K j a) = shortImage K j a :=
    short_transport K j a
  change c (centralWord K v) = _
  simp only [centralWord,centralCoordinates,higherWord,map_mul,hc,shortImage]
  change positiveModel K 3 (v 0)*positiveModel K 2 (-v 1)*positiveModel K 1 (-0)*
      positiveModel K 5 (v 2) =
    positiveModel K 2 (-v 1)*positiveModel K 3 (v 0)*positiveModel K 4 0*
      positiveModel K 5 (v 2)
  simp only [neg_zero,positiveModel_zero,mul_one]
  have he := (higher_commute K 0 1 (-v 1) (v 0)).eq
  change positiveModel K 2 (-v 1)*positiveModel K 3 (v 0) =
    positiveModel K 3 (v 0)*positiveModel K 2 (-v 1) at he
  rw [←he]

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralWords
