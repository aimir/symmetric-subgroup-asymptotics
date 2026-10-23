import SymmetricSubgroupAsymptotics.CFSGHermitianPairTransport
import Mathlib.Tactic.Ring

/-! Over a field with a nonidentity coefficient automorphism, a linear
subspace on which every Hermitian norm vanishes is totally orthogonal.
The proof uses two scalar tests and never divides by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTotallyIsotropic
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem norm_zeroOn_iff_pair_zeroOn (sigma : K ≃+* K)
    (hnonfixed : ∃ a : K, sigma a ≠ a) (H : Matrix I I K) (S : Submodule K (I → K)) :
    (∀ x ∈ S, hermitianPair sigma H x x = 0) ↔
      ∀ x ∈ S, ∀ y ∈ S, hermitianPair sigma H x y = 0 := by
  constructor
  · intro hnorm
    have hsum (x : I → K) (hx : x ∈ S) (y : I → K) (hy : y ∈ S) :
        hermitianPair sigma H x y + hermitianPair sigma H y x = 0 := by
      have hh := hnorm (x + y) (S.add_mem hx hy)
      simpa only [hermitianPair_add_left, hermitianPair_add_right,
        hnorm x hx, hnorm y hy, zero_add, add_zero, add_comm] using hh
    obtain ⟨a, ha⟩ := hnonfixed
    intro x hx y hy
    have hxy := hsum x hx y hy
    have hscaled := hsum (a • x) (S.smul_mem a hx) y hy
    have hleft := hermitianPair_smul sigma H a 1 x y
    have hright := hermitianPair_smul sigma H 1 a y x
    simp only [one_smul, map_one, mul_one, one_mul] at hleft hright
    rw [hleft, hright] at hscaled
    have hz : (sigma a - a) * hermitianPair sigma H x y = 0 := by
      calc
        _ = (sigma a * hermitianPair sigma H x y + a * hermitianPair sigma H y x) -
            a * (hermitianPair sigma H x y + hermitianPair sigma H y x) := by ring
        _ = 0 := by rw [hscaled, hxy, mul_zero, sub_zero]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)
  · intro h x hx
    exact h x hx x hx

end SymmetricSubgroupAsymptotics.CFSGHermitianTotallyIsotropic
