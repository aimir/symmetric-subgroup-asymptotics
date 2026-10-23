import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSignDuality
import SymmetricSubgroupAsymptotics.CFSGGTwoSimpleBruhatComplement

/-! The complete twelve-direction Weyl action, retaining the root sign
and the parameter sign. The negative half is derived by the actual
whole-model sign-duality, not inferred from unsigned root labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSignedWeylTransport
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalSignDuality CFSGGTwoOriginalSimpleWeylTransport
open CFSGGTwoSimpleBruhatComplement
variable (K : Type) [Field K] [CharP K 3]

def shortTarget (j : Fin 6) : Fin 6 :=
  match j.val with
  | 0=>0 | 1=>4 | 2=>3 | 3=>2 | 4=>1 | _=>5

def longTarget (j : Fin 6) : Fin 6 :=
  match j.val with
  | 0=>2 | 1=>1 | 2=>0 | 3=>3 | 4=>5 | _=>4

def targetIndex (i : Fin 2) (j : Fin 6) : Fin 6 :=
  if i=0 then shortTarget j else longTarget j

def flipsSign (i : Fin 2) (j : Fin 6) : Bool :=
  if i=0 then decide (j=0) else decide (j=1)

def targetSign (i : Fin 2) (neg : Bool) (j : Fin 6) : Bool :=
  if flipsSign i j then !neg else neg

def shortCoefficient (j : Fin 6) : K :=
  if j=0 ∨ j=3 ∨ j=4 then -1 else 1

def longCoefficient (j : Fin 6) : K :=
  if j=1 ∨ j=2 ∨ j=5 then -1 else 1

def coefficient (i : Fin 2) (j : Fin 6) : K :=
  if i=0 then shortCoefficient K j else longCoefficient K j

theorem coefficient_sq (i : Fin 2) (j : Fin 6) :
    coefficient K i j*coefficient K i j=1 := by
  unfold coefficient shortCoefficient longCoefficient
  split_ifs <;> simp

theorem targetIndex_involutive (i : Fin 2) (j : Fin 6) :
    targetIndex i (targetIndex i j)=j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem targetSign_complement (i : Fin 2) (neg : Bool) (j : Fin 6) :
    targetSign i (!neg) j=!(targetSign i neg j) := by
  unfold targetSign
  split_ifs <;> simp

theorem signDual_simple (i : Fin 2) :
    signDual K (simpleWeyl K i)=simpleWeyl K i := by
  fin_cases i
  · exact signDual_shortWord K
  · exact signDual_longWord K

private theorem positive_transport (i : Fin 2) (j : Fin 6) (t : K) :
    simpleWeyl K i*signedModel K false j t*(simpleWeyl K i)⁻¹=
      signedModel K (targetSign i false j) (targetIndex i j) (coefficient K i j*t) := by
  rw [signedModel_positive]
  fin_cases i
  · change shortWord K*positiveModel K j t*(shortWord K)⁻¹=_
    rw [short_transport]
    fin_cases j <;>
      simp [shortImage,targetSign,flipsSign,targetIndex,shortTarget,coefficient,
        shortCoefficient,signedModel,positiveModel,directionModel,
        CFSGGTwoPositiveDirections.rootNode]
  · change longWord K*positiveModel K j t*(longWord K)⁻¹=_
    rw [long_transport]
    fin_cases j <;>
      simp [longImage,targetSign,flipsSign,targetIndex,longTarget,coefficient,
        longCoefficient,signedModel,positiveModel,directionModel,
        CFSGGTwoPositiveDirections.rootNode]

theorem signed_transport (i : Fin 2) (neg : Bool) (j : Fin 6) (t : K) :
    simpleWeyl K i*signedModel K neg j t*(simpleWeyl K i)⁻¹=
      signedModel K (targetSign i neg j) (targetIndex i j) (coefficient K i j*t) := by
  cases neg
  · exact positive_transport K i j t
  · have he := congrArg (signDual K) (positive_transport K i j (-t))
    simp only [map_mul,map_inv,signDual_simple,signDual_signedModel,Bool.not_false,
      neg_neg,mul_neg] at he
    rw [show targetSign i true j=!(targetSign i false j) from
      targetSign_complement i false j]
    simpa only [neg_neg] using he

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSignedWeylTransport
