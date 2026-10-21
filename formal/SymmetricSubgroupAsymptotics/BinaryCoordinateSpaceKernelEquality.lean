import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import Mathlib.Algebra.Field.ZMod

/-! A reversible chart equals a literal constraint kernel when the
chart's defect factors through those constraints. Only individual basis
columns are needed; no enumeration of all coordinate vectors occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCoordinateSpace
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem space_eq_ker_of_basis_factor {n d q : ℕ}
    (C : BinaryCoordinateSpace n d)
    (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2))
    (L : (Fin q → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hzero : ∀ j, A (C.inclusion (Pi.single j 1)) = 0)
    (hfactor : ∀ j : Fin n,
      C.inclusion (C.coordinates (Pi.single j 1)) - Pi.single j 1 = L (A (Pi.single j 1))) :
    C.space = A.ker := by
  have he : C.inclusion.comp C.coordinates - LinearMap.id = L.comp A := by
    apply LinearMap.pi_ext
    intro j c
    have hs : (Pi.single j c : Fin n → ZMod 2) = c • Pi.single j (1 : ZMod 2) := by
      funext i
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hs, map_smul, ← smul_sub, hfactor]
  apply le_antisymm
  · apply C.le_of_basis_mem
    intro j
    exact hzero j
  · intro v hv
    have hz : A v = 0 := hv
    have he' := DFunLike.congr_fun he v
    change C.inclusion (C.coordinates v) - v = L (A v) at he'
    rw [hz, map_zero] at he'
    exact (C.mem_iff v).mpr (sub_eq_zero.mp he')

end SymmetricSubgroupAsymptotics.BinaryCoordinateSpace
