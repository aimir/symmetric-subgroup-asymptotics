import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceTransport

/-! Transport of the literal source Cartan table changes no image
submodule in the target matrix space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

theorem transportSource_baseChange_range_eq (h : A = B) (D : Data A I)
    (K : Type) [CommRing K] :
    (baseChange (transportSource h D) K).range = (baseChange D K).range := by
  cases h
  rfl

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
