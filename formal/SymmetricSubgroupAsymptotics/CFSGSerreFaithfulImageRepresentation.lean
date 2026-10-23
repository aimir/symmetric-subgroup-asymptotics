import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions

/-! Injectivity of the SAME original tensor map makes its induced image
action faithful. This is a source-level statement, not a simplicity
argument or a converse inferred from equality of image ranges. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreFaithfulImageRepresentation
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
  {I : Type*} [Fintype I] [DecidableEq I]
  (D : Data A I) (K : Type) [Field K]

theorem imageRepresentation_injective (hf : Function.Injective (baseChange D K)) :
    Function.Injective (imageRepresentation D K) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply hf
  have hh := congrArg (fun f : (baseChange D K).range ≃ₗ[K] (baseChange D K).range =>
    (f ((baseChange D K).rangeRestrict x)).val) he
  simpa only [imageRepresentation_intertwines] using hh

end SymmetricSubgroupAsymptotics.CFSGSerreFaithfulImageRepresentation
