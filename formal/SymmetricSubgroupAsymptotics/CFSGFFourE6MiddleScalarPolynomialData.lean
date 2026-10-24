import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries

/-! A computable sparse exponent-list language for one selected middle
Weyl residual column. Equality is certified by finite parity counts,
without invoking noncomputable polynomial-ring arithmetic. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarPolynomialData
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6NormQuotientCoefficientPilot

abbrev Exponent := ℕ×ℕ
abbrev Action := (Bool×Fin 4)×Exponent

def linearCoefficient (a : Action) (j k : Fin 26) : ZMod 2 :=
  let r := if a.1.1 then negativeLabel (columnLabels j) else columnLabels j
  let s := if a.1.1 then negativeLabel (columnLabels k) else columnLabels k
  (normEntry (if a.1.2=1 then shortFirst else longFirst) r s : ZMod 2)

def quadraticCoefficient (a : Action) (j k : Fin 26) : ZMod 2 :=
  let r := if a.1.1 then negativeLabel (columnLabels j) else columnLabels j
  let s := if a.1.1 then negativeLabel (columnLabels k) else columnLabels k
  (normEntry (if a.1.2=1 then shortSecond else longSecond) r s : ZMod 2)

def shift (p : Exponent) (l : List Exponent) : List Exponent :=
  l.map fun e=>(p.1+e.1,p.2+e.2)

def scaledShift (n : ℕ) (p : Exponent) (l : List Exponent) : List Exponent :=
  (List.replicate n (shift p l)).flatten

def stepContributions (a : Action) (v : Fin 26→List Exponent) (j : Fin 26) : List Exponent :=
  v j ++ (List.finRange 26).flatMap fun k=>
    scaledShift (linearCoefficient a j k).val a.2 (v k) ++
      scaledShift (quadraticCoefficient a j k).val (2*a.2.1,2*a.2.2) (v k)

def parityTransition (a : Action) (v w : Fin 26→List Exponent) : Prop :=
  ∀j : Fin 26,∀e ∈ (stepContributions a v j).toFinset∪(w j).toFinset,
    (stepContributions a v j).count e%2=(w j).count e%2

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarPolynomialData
