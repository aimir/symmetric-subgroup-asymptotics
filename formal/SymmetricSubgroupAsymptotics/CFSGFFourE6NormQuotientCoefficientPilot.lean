import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientRootMatching

/-! Selected finite coefficient pilot for positive short node 1 and
positive long node 2. The entries are the normalized simply-laced
root-step formulas, evaluated only at the selected 26 labels. This
module certifies the finite arithmetic; identifying these formulas
with the actual integral Geck operators is a separate bridge. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoefficientPilot
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching CFSGIntegerMatrixPairing
local instance : Fintype PairIndex := by unfold PairIndex;infer_instance
local instance : DecidableEq PairIndex := by unfold PairIndex;infer_instance

abbrev RawIndex := Fin 6⊕(Fin 6→ℤ)

def normIndex : PairIndex→RawIndex
  | .inl j=>.inl (cartanRepresentative j)
  | .inr r=>.inr r.val

def fixedIndex : PairIndex→RawIndex
  | .inl j=>.inl (fixedCartanRepresentative j)
  | .inr r=>.inr (dualRoot r.val)

def partnerIndex : RawIndex→RawIndex
  | .inl j=>.inl (CFSG.Models.e6Twist j)
  | .inr r=>.inr (twistVector r)

def simpleVector (i:Fin 6) : Fin 6→ℤ := Pi.single i 1

def stepEntry (i:Fin 6) : RawIndex→RawIndex→ℤ
  | .inl _,.inl _=>0
  | .inl j,.inr r=>if j=i ∧ r= -simpleVector i then 1 else 0
  | .inr r,.inl j=>if r=simpleVector i then |CartanMatrix.E₆ i j| else 0
  | .inr r,.inr s=>if r=simpleVector i+s then 1 else 0

def secondEntry (i:Fin 6) : RawIndex→RawIndex→ℤ
  | .inr r,.inr s=>if r=simpleVector i ∧ s= -simpleVector i then 1 else 0
  | _,_=>0

def orthogonalProductEntry (i j:Fin 6) : RawIndex→RawIndex→ℤ
  | .inr r,.inr s=>if integerPairing CartanMatrix.E₆ (simpleVector j+s) (simpleVector j+s)=2 ∧
      r=simpleVector i+(simpleVector j+s) then 1 else 0
  | _,_=>0

def shortFirst (r s:RawIndex) : ℤ := stepEntry 2 r s+stepEntry 4 r s
def longFirst (r s:RawIndex) : ℤ := stepEntry 3 r s
def shortSecond (r s:RawIndex) : ℤ :=
  secondEntry 2 r s+secondEntry 4 r s+orthogonalProductEntry 2 4 r s
def longSecond (r s:RawIndex) : ℤ := secondEntry 3 r s

def normCoefficient (T:RawIndex→RawIndex→ℤ) (j k:PairIndex) : ℤ :=
  T (normIndex j) (normIndex k)+T (normIndex j) (partnerIndex (normIndex k))

def quotientCoefficient (T:RawIndex→RawIndex→ℤ) (j k:PairIndex) : ℤ :=
  T (fixedIndex j) (fixedIndex k)

theorem short_quotient_linear_zero : ∀j k:PairIndex,
    quotientCoefficient shortFirst j k%2=0 := by decide +kernel

theorem short_quotient_quadratic_eq_long_norm_linear : ∀j k:PairIndex,
    quotientCoefficient shortSecond j k%2=normCoefficient longFirst j k%2 := by decide +kernel

theorem long_norm_quadratic_zero : ∀j k:PairIndex,
    normCoefficient longSecond j k%2=0 := by decide +kernel

theorem long_quotient_linear_eq_short_norm_linear : ∀j k:PairIndex,
    quotientCoefficient longFirst j k%2=normCoefficient shortFirst j k%2 := by decide +kernel

theorem long_quotient_quadratic_eq_short_norm_quadratic : ∀j k:PairIndex,
    quotientCoefficient longSecond j k%2=normCoefficient shortSecond j k%2 := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoefficientPilot
