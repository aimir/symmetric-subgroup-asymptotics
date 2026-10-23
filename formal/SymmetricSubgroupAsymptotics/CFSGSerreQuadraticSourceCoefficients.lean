import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceTransport

/-! The coefficient matrices are unchanged when only the literal source
Cartan index of a realization is transported along a proved equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

theorem transportSource_integerGenerator (h : A=B) (D : Data A I)
    (g : CartanMatrix.Generators (Fin n)) :
    (transportSource h D).integerGenerator g=D.integerGenerator g := by
  cases h
  rfl

theorem transportSource_integerRoot (h : A=B) (D : Data A I) (neg : Bool) (i : Fin n) :
    integerRoot (transportSource h D) neg i=integerRoot D neg i := by
  cases h
  rfl

theorem transportSource_integerSecond (h : A=B) (D : Data A I) (neg : Bool) (i : Fin n) :
    (transportSource h D).integerSecond neg i=D.integerSecond neg i := by
  cases h
  rfl

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
