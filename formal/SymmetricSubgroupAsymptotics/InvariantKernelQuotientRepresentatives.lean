import SymmetricSubgroupAsymptotics.InvariantKernelSmallStabilizer
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel

/-! Stabilizer counts are constant on cosets of the same original module
state modulo whose radical they are measured. Sparse quotient coordinates
therefore reduce point tests from2^16 assignments to at most2^8. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

/-- A sparse basis test verifies the original quotient-coordinate defect. -/
theorem linear_quotient_defect_mem_of_basis
    {k : Type} [Field k] {w d : ℕ}
    (W : Submodule k (Fin w → k))
    (projection : (Fin w → k) →ₗ[k] (Fin d → k))
    (sectionMap : (Fin d → k) →ₗ[k] (Fin w → k))
    (hbasis : ∀ i, Pi.single i 1 - sectionMap (projection (Pi.single i 1)) ∈ W)
    (v : Fin w → k) : v - sectionMap (projection v) ∈ W := by
  let defect := LinearMap.id - sectionMap.comp projection
  have hv : (∑ i, v i • Pi.single i (1 : k)) = v := by
    ext j
    simp [Pi.single_apply, mul_ite]
  change defect v ∈ W
  rw [← hv, map_sum]
  apply W.sum_mem
  intro i _
  rw [map_smul]
  exact W.smul_mem _ (hbasis i)

/-- Counts on a sparse quotient section control every original point.
The state and radical retain their original embeddings in V. -/
theorem stabilizer_count_le_of_quotient_representatives
    {k H V C : Type*} [Field k] [Group H]
    [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
    {r : ℕ} (row : Fin r → H) (rho : Representation k H V)
    (W R : Submodule k V)
    (projection : V →ₗ[k] C) (sectionMap : C →ₗ[k] V)
    (hdefect : ∀ v, v - sectionMap (projection v) ∈ W)
    (hkill : ∀ i, ∀ v ∈ W, rho (row i) v - v ∈ R)
    (cap : ℕ)
    (hcount : ∀ c : C, c ≠ 0 →
      Nat.card {i : Fin r // rho (row i) (sectionMap c) - sectionMap c ∈ R} ≤ cap)
    (v : V) (hv : v ∉ W) :
    Nat.card {i : Fin r // rho (row i) v - v ∈ R} ≤ cap := by
  have hc : projection v ≠ 0 := by
    intro hz
    have hd := hdefect v
    rw [hz, map_zero, sub_zero] at hd
    exact hv hd
  have hiff (i : Fin r) : rho (row i) v - v ∈ R ↔
      rho (row i) (sectionMap (projection v)) - sectionMap (projection v) ∈ R := by
    have hd : (rho (row i) v - v) -
        (rho (row i) (sectionMap (projection v)) - sectionMap (projection v)) ∈ R := by
      have hh := hkill i _ (hdefect v)
      rw [map_sub] at hh
      convert hh using 1 <;> abel
    constructor
    · intro h
      convert R.sub_mem h hd using 1 <;> abel
    · intro h
      simpa only [sub_add_cancel] using R.add_mem hd h
  let e : {i : Fin r // rho (row i) v - v ∈ R} ≃
      {i : Fin r // rho (row i) (sectionMap (projection v)) - sectionMap (projection v) ∈ R} := {
    toFun i := ⟨i.val, (hiff i.val).mp i.property⟩
    invFun i := ⟨i.val, (hiff i.val).mpr i.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).le.trans (hcount _ hc)

end SymmetricSubgroupAsymptotics
