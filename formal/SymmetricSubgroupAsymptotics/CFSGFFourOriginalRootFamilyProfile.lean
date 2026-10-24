import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFiftyTwoFamily
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathComposition

/-! Actual source slots and weights for the whole-family F4 certificate:
24 positive divided-power paths plus four signed Cartan slots. All source
weights and every positive-weight comparison direction are discharged
here. Finite action coefficients and parent certificates remain separate;
no spanning, basis or representation injectivity is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyProfile
open CFSG.Models.Chevalley CFSGFFourOriginalFiftyTwoFamily CFSGSerreSignedRootWeights
local notation "A" => CartanMatrix.F₄

abbrev Slot := (Fin 24)⊕(Fin 4)

def family (neg:Bool) : Slot→RationalLie A :=
  Sum.elim (fun j=>(rootVectors neg j).val) (coroot A neg)

def rootHeight (j:Fin 24) : ℕ := (∑i:Fin 4,degree j i).toNat

def height : Slot→ℕ := Sum.elim rootHeight (fun _=>0)

def integerWeight (a:Fin 4) : Slot→ℤ := Sum.elim (simpleWeight a) (fun _=>0)

def weight (a:Fin 4) (j:Slot) : ℚ := integerWeight a j

def simpleIndex (i:Fin 4) : Fin 24 := ![3,2,1,0] i

theorem rootHeight_positive : ∀j:Fin 24,0<rootHeight j := by decide +kernel

theorem simple_height : ∀i:Fin 4,height (.inl (simpleIndex i))=1 := by decide +kernel

theorem simple_value (neg:Bool) (i:Fin 4) :
    family neg (.inl (simpleIndex i))=rootVector A neg i := by
  fin_cases i <;> rfl

theorem family_weight (neg:Bool) (a:Fin 4) (j:Slot) :
    ⁅coroot A neg a,family neg j⁆=weight a j • family neg j := by
  cases j with
  | inl j=>exact rootVectors_weight neg a j
  | inr b=>
    change ⁅coroot A neg a,coroot A neg b⁆=(0:ℚ) • coroot A neg b
    rw [zero_smul]
    exact coroots_commute A neg a b

private theorem positive_comparison_integer : ∀i:Fin 4,∀j:Fin 24,
    ∃a:Fin 4,0<A a i+simpleWeight a j := by decide +kernel

theorem positive_comparison (i:Fin 4) (j:Slot) (hj:0<height j) :
    ∃a:Fin 4,0<(A a i:ℚ)+weight a j := by
  cases j with
  | inl j=>
    obtain ⟨a,ha⟩:=positive_comparison_integer i j
    refine ⟨a,?_⟩
    change 0<(A a i:ℚ)+(simpleWeight a j:ℚ)
    exact_mod_cast ha
  | inr b=>exact (Nat.lt_irrefl 0 hj).elim

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyProfile
