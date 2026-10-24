import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFullCoefficientCertificate

/-! Integer entries on all52 original source labels. Root slots retain
their signs; signed Cartan vectors are converted back to the four literal
H generators. The two sparse-string certificates prove an integral
half-square and vanishing cube, without any matrix representation or
source-basis assumption. Source action is bound separately. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedActionEntries
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalRootFamilyProfile
open CFSGFFourOriginalFullCoefficientCertificate
local notation "A" => CartanMatrix.F₄

def slotIndex (neg:Bool) : Slot→BasisIndex
  | .inl j=>.inl (neg,j)
  | .inr b=>.inr b

def slotCoefficient (neg:Bool) : Slot→ℤ
  | .inl _=>1
  | .inr _=>if neg then -1 else 1

def convertEntry (neg:Bool) (u:Slot×ℤ) : BasisIndex×ℤ :=
  (slotIndex neg u.1,u.2*slotCoefficient neg u.1)

def signedEntry (neg:Bool) (i:Fin 4) : BasisIndex→BasisIndex×ℤ
  | .inl (s,j)=>if s=neg then convertEntry s (raisingEntry i (.inl j))
      else convertEntry s (loweringEntry i (.inl j))
  | .inr b=>(.inl (neg,simpleIndex i),if neg then A b i else -A b i)

def squareEntry (neg:Bool) (i:Fin 4) (j:BasisIndex) : BasisIndex×ℤ :=
  let u:=signedEntry neg i j
  let v:=signedEntry neg i u.1
  (v.1,(u.2*v.2)/2)

theorem second_coefficient_even : ∀(neg:Bool)(i:Fin 4)(j:BasisIndex),
    (signedEntry neg i j).2*(signedEntry neg i (signedEntry neg i j).1).2=
      2*(squareEntry neg i j).2 := by decide +kernel

theorem third_coefficient_zero : ∀(neg:Bool)(i:Fin 4)(j:BasisIndex),
    (signedEntry neg i j).2*(signedEntry neg i (signedEntry neg i j).1).2*
      (signedEntry neg i (signedEntry neg i (signedEntry neg i j).1).1).2=0 := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedActionEntries
