import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! Four genuine fixed simple-orbit tests, uniformly for every field
automorphism. Their actual first-height coordinates prove nontriviality
in every characteristic, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSimpleTests
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private def simplePositive (K : Type) [Field K] (i : Fin 6) : Positive K :=
  positiveRoot A hd hs hp ho K i 1

def orbitPositive (K : Type) [Field K] (a : Fin 4) : Positive K :=
  ![simplePositive K 0*simplePositive K 5,
    simplePositive K 2*simplePositive K 4,simplePositive K 3,simplePositive K 1] a

theorem orbitPositive_val (K : Type) [Field K] (a : Fin 4) :
    (orbitPositive K a).val=orbitParameter K false a 1 := by
  fin_cases a <;> rfl

def testCoordinate (a : Fin 4) : Fin 6 := ![0,2,3,1] a

theorem orbitPositive_leading (K : Type) [Field K] (a : Fin 4) :
    leadingCoordinates A hd hs hp ho K (orbitPositive K a).val (testCoordinate a)=1 := by
  change (leadingHom A hd hs hp ho K (orbitPositive K a)).toAdd (testCoordinate a)=1
  fin_cases a
  · change (leadingHom A hd hs hp ho K (simplePositive K 0*simplePositive K 5)).toAdd 0=1
    have hm := congrArg (fun x : Multiplicative (Fin 6→K)=>x.toAdd 0)
      ((leadingHom A hd hs hp ho K).map_mul (simplePositive K 0) (simplePositive K 5))
    dsimp only [simplePositive] at hm
    rw [leadingHom_positiveRoot A hd hs hp ho K 0 1,
      leadingHom_positiveRoot A hd hs hp ho K 5 1] at hm
    exact hm.trans (by simp)
  · change (leadingHom A hd hs hp ho K (simplePositive K 2*simplePositive K 4)).toAdd 2=1
    have hm := congrArg (fun x : Multiplicative (Fin 6→K)=>x.toAdd 2)
      ((leadingHom A hd hs hp ho K).map_mul (simplePositive K 2) (simplePositive K 4))
    dsimp only [simplePositive] at hm
    rw [leadingHom_positiveRoot A hd hs hp ho K 2 1,
      leadingHom_positiveRoot A hd hs hp ho K 4 1] at hm
    exact hm.trans (by simp)
  · change (leadingHom A hd hs hp ho K (simplePositive K 3)).toAdd 3=1
    simp only [simplePositive,leadingHom_positiveRoot]
    change (Pi.single 3 (1:K) : Fin 6→K) 3=1
    simp
  · change (leadingHom A hd hs hp ho K (simplePositive K 1)).toAdd 1=1
    simp only [simplePositive,leadingHom_positiveRoot]
    change (Pi.single 1 (1:K) : Fin 6→K) 1=1
    simp

theorem orbitParameter_one_ne_one (K : Type) [Field K] (a : Fin 4) :
    orbitParameter K false a 1≠1 := by
  intro he
  have hc := orbitPositive_leading K a
  rw [orbitPositive_val,he] at hc
  have hz := congrFun (leadingCoordinates_one A hd hs hp ho K) (testCoordinate a)
  exact zero_ne_one (hz.symm.trans hc)

theorem orbitParameter_one_mem_signedFixed (K : Type) [Field K] (sigma : K≃+*K)
    (a : Fin 4) : orbitParameter K false a 1∈signedFixed K sigma false :=
  ⟨orbitParameter_mem_upper K false a 1,orbitParameter_fixed K sigma false a 1 (map_one sigma)⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSimpleTests
