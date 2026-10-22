import SymmetricSubgroupAsymptotics.CFSGSkewOrthogonalKernels
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Lean.Elab.Tactic.Omega

/-! Equal-dimensional subspaces have equal cross-orthogonal-axis
dimensions for an actual nondegenerate symmetric bilinear form. This
removes a redundant second dimension premise in the R12 case. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarCrossAxisDimensions
open CFSGSkewOrthogonalKernels
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem cross_axis_finrank_eq (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (P Q : Submodule K V)
    (hd : Module.finrank K P = Module.finrank K Q) :
    Module.finrank K (P ⊓ B.orthogonal Q : Submodule K V) =
      Module.finrank K (Q ⊓ B.orthogonal P : Submodule K V) := by
  let S : Submodule K V := P ⊔ B.orthogonal Q
  let A : Submodule K V := P ⊓ B.orthogonal Q
  let C : Submodule K V := Q ⊓ B.orthogonal P
  have hr : B.IsRefl := fun x y h => (hs y x).trans h
  have ho : B.orthogonal S = C := by
    change B.orthogonal (P ⊔ B.orthogonal Q) = Q ⊓ B.orthogonal P
    rw [orthogonal_sup, B.orthogonal_orthogonal hB hr Q, inf_comm]
  have hoDim := congrArg (fun T : Submodule K V => Module.finrank K T) ho
  dsimp only at hoDim
  have hQ := B.finrank_add_finrank_orthogonal' Q
  rw [hB.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at hQ
  change Module.finrank K Q + Module.finrank K (B.orthogonal Q) = Module.finrank K V at hQ
  have hS := B.finrank_add_finrank_orthogonal' S
  rw [hB.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at hS
  change Module.finrank K S + Module.finrank K (B.orthogonal S) = Module.finrank K V at hS
  change Module.finrank K (B.orthogonal S) = Module.finrank K C at hoDim
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P (B.orthogonal Q)
  change Module.finrank K S + Module.finrank K A =
    Module.finrank K P + Module.finrank K (B.orthogonal Q) at hsum
  change Module.finrank K A = Module.finrank K C
  omega

end SymmetricSubgroupAsymptotics.CFSGPolarCrossAxisDimensions
