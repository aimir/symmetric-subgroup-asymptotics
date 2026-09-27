import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SymmetricSubgroupAsymptotics.OrbitProfileProduct

/-! Finite products preserve the actual p-group property. This installs
binaryity for an original orbit-profile exterior from its actual actions,
without a common exponent or finite-order bound as an input. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

theorem finitePi_isPGroup {p : ℕ} {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, Group (G i)] (hG : ∀ i, IsPGroup p (G i)) :
    IsPGroup p (∀ i, G i) := by
  intro f
  choose k hk using fun i => hG i (f i)
  let N := ∑ i, k i
  refine ⟨N,?_⟩
  funext i
  have hle : k i≤N :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  have he : N=k i+(N-k i) := (Nat.add_sub_of_le hle).symm
  change (f i)^(p^N)=1
  rw [he,pow_add,pow_mul,hk i,one_pow]

theorem orbitProfileProduct_isPGroup {p : ℕ} {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (hU : ∀ i, IsPGroup p (U i)) : IsPGroup p (OrbitProfileProductGroup m U) :=
  finitePi_isPGroup (fun i => Fin (m i) → U i)
    (fun i => finitePi_isPGroup (fun _ : Fin (m i) => U i) (fun _ => hU i))

end SymmetricSubgroupAsymptotics

end

