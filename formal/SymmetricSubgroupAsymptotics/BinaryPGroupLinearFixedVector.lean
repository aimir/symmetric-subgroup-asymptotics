import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A binary finite-dimensional module for an actual two-group has a
nonzero fixed vector. This is a counting theorem, not an irreducibility
assumption. It will be applied to the actual translation subgroup of a
regular norm-curve basis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPGroupLinearFixedVector

variable {K V G : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Nontrivial V] [Group G]

theorem exists_nonzero_fixed (hK : Nat.card K=2) (hG : IsPGroup 2 G)
    (ρ : G →* (V ≃ₗ[K] V)) : ∃ v : V, v≠0 ∧ ∀ g : G, ρ g v=v := by
  letI : Finite V := Module.finite_of_finite K
  letI : MulAction G V := {
    smul := fun g v => ρ g v
    one_smul := fun v => by
      change ρ 1 v=v
      rw [map_one]
      rfl
    mul_smul := fun g h v => by
      change ρ (g*h) v=ρ g (ρ h v)
      rw [map_mul]
      rfl }
  have hdim : 0<Module.finrank K V := Module.finrank_pos
  have hcard : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := V),hK]
    obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdim)
    refine ⟨2^d,?_⟩
    rw [hd,pow_succ]
    omega
  have hzero : (0 : V) ∈ MulAction.fixedPoints G V := by
    intro g
    exact map_zero (ρ g)
  obtain ⟨v,hv,hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard hzero
  exact ⟨v,Ne.symm hne,fun g => hv g⟩

end SymmetricSubgroupAsymptotics.BinaryPGroupLinearFixedVector
