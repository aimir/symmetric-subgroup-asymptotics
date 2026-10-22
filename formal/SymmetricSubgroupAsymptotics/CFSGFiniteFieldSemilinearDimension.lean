import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! Actual semilinear equivalences preserve subspace dimension over a
finite field, by their literal cardinal bijection. No scalar restriction
or dimension-identification hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldSemilinearDimension
variable {K V : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

theorem subspace_card (P : Submodule K V) : Nat.card P=Nat.card K^Module.finrank K P := by
  let e : P≃ₗ[K](Fin (Module.finrank K P)→K) := LinearEquiv.ofFinrankEq _ _ (by simp)
  rw [Nat.card_congr e.toEquiv,Nat.card_fun,Nat.card_fin]

theorem finrank_map (σ : K≃+*K) (e : V≃ₛₗ[σ.toRingHom]V) (P : Submodule K V) :
    Module.finrank K (P.map e.toLinearMap)=Module.finrank K P := by
  have hc := Nat.card_congr (e.submoduleMap P).toEquiv
  rw [subspace_card,subspace_card] at hc
  exact (Nat.pow_right_injective (Nat.succ_le_iff.mpr
    (Finite.one_lt_card : 1<Nat.card K)) hc).symm

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldSemilinearDimension
