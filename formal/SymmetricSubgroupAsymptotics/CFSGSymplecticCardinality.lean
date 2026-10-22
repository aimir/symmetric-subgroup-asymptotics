import SymmetricSubgroupAsymptotics.CFSGSymplecticRankOneCardinality

/-! The exact natural symplectic order follows from the proved rank-one
column chart and the literal hyperbolic-pair stabilizer recurrence. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K] [Finite K]

 theorem elementary_card (n : ℕ) :
    Nat.card (elementaryRootGroup K n) =
      Nat.card K ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card K ^ (2 * (i + 1)) - 1) := by
  induction n with
  | zero =>
    have hzero : Nat.card (elementaryRootGroup K 0) = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨1, ?_⟩
      intro u
      apply Subtype.ext
      apply Units.ext
      ext i j
      cases i <;> exact Fin.elim0 ‹Fin 0›
    simpa only [Nat.zero_mul, pow_zero, Finset.range_zero, Finset.prod_empty, one_mul] using hzero
  | succ n ih =>
    cases n with
    | zero =>
      simpa [Finset.prod_range_succ, Nat.mul_comm] using elementary_rankOne_card K
    | succ r =>
      rw [elementary_card_recurrence K (r + 1) (by omega), ih,
        Finset.prod_range_succ (fun i : ℕ => Nat.card K ^ (2 * (i + 1)) - 1) (r + 1)]
      have he : (r + 1 + 1) * (r + 1 + 1) =
          (2 * (r + 1 + 1) - 1) + (r + 1) * (r + 1) := by
        have hsub : 2 * (r + 1 + 1) - 1 = 2 * r + 3 := by omega
        rw [hsub]
        ring
      rw [he, pow_add]
      ring

 theorem symplectic_card (n : ℕ) :
    Nat.card (Matrix.symplecticGroup (Fin n) K) =
      Nat.card K ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card K ^ (2 * (i + 1)) - 1) := by
  rw [← Nat.card_congr (elementarySymplecticEquiv K n).toEquiv, elementary_card]

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
