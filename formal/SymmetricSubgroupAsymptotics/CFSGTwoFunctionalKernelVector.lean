import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-! Two actual linear equations cannot kill a subspace of dimension
at least three. The witness remains in the original submodule. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoFunctionalKernelVector
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_nonzero_common_kernel (P : Submodule K V) (hdim : 3 ≤ Module.finrank K P)
    (f g : V →ₗ[K] K) : ∃ x : V, x ∈ P ∧ x ≠ 0 ∧ f x = 0 ∧ g x = 0 := by
  let a : P →ₗ[K] K × K := (f.comp P.subtype).prod (g.comp P.subtype)
  have hr : Module.finrank K a.range ≤ 2 := by
    simpa only [Module.finrank_prod, Module.finrank_self] using Submodule.finrank_le a.range
  have he := a.finrank_range_add_finrank_ker
  have hk : 1 ≤ Module.finrank K a.ker := by omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := a.ker)
    (Submodule.one_le_finrank_iff.mp hk)
  have hf : f z.val = 0 := congrArg Prod.fst (show a z = 0 from hz)
  have hg : g z.val = 0 := congrArg Prod.snd (show a z = 0 from hz)
  refine ⟨z.val, z.property, ?_, hf, hg⟩
  intro h
  exact hz0 (Subtype.ext h)

end SymmetricSubgroupAsymptotics.CFSGTwoFunctionalKernelVector
