import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Quotient.Defs

/-! Kernels of actions on equal submodules can be compared using their
literal values in the ambient module. This avoids reducing large source
realizations or constructing new transported action representations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubmoduleActionKernelTransport
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

theorem kernel_le_of_shared_values (P Q : Submodule K V) (hPQ : P = Q)
    (a : G →* (P ≃ₗ[K] P)) (b : G →* (Q ≃ₗ[K] Q))
    (F : G → V → V)
    (ha : ∀ g x, (a g x).val = F g x.val)
    (hb : ∀ g x, (b g x).val = F g x.val) : a.ker ≤ b.ker := by
  intro g hg
  change b g = 1
  apply LinearEquiv.ext
  intro y
  have hy : y.val ∈ P := hPQ.symm ▸ y.property
  let x : P := ⟨y.val, hy⟩
  have hx := congrArg (fun e : P ≃ₗ[K] P => (e x).val) hg
  change (a g x).val = x.val at hx
  apply Subtype.ext
  rw [hb]
  exact (ha g x).symm.trans hx

end SymmetricSubgroupAsymptotics.CFSGSubmoduleActionKernelTransport
