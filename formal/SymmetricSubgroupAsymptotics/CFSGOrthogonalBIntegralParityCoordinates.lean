import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanMatrices

/-! The natural integral B coroots lie in an even-sum toral lattice.
The final simple coroot is twice an integral diagonal matrix. Hence a
primitive Z-coordinate functional on the FULL matrix module is impossible;
source splitting must use the intrinsic parity lattice or invert 2. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntegralParityCoordinates
open CFSGOrthogonalBSerreMatrices

/-- Sum of the positive-half diagonal coordinates; not the full matrix trace. -/
def positiveTrace (R : Type*) [CommRing R] (r : ℕ) : Mat R r →ₗ[R] R where
  toFun M := ∑ i : Fin r, M (pos r i) (pos r i)
  map_add' M N := by simp [Finset.sum_add_distrib]
  map_smul' a M := by simp [Finset.mul_sum]

/-- The nonterminal simple coroots have toral sum zero; the terminal one
has toral sum two, in exactly the pinned B-transpose convention. -/
theorem positiveTrace_cartan (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) :
    positiveTrace R r (cartan R r i) = if i.val + 1 < r then 0 else 2 := by
  rw [cartan_eq]
  split_ifs with h
  · simp [positiveTrace, Matrix.single, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, pos, neg]
  · simp [positiveTrace, Matrix.single, Finset.sum_sub_distrib, pos, neg]

/-- The actual integral toral parity condition. -/
def evenTraceSpace (r : ℕ) : Submodule ℤ (Mat ℤ r) :=
  (((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ).range).comap (positiveTrace ℤ r)

theorem cartan_mem_evenTraceSpace (r : ℕ) (i : Fin r) :
    cartan ℤ r i ∈ evenTraceSpace r := by
  change ∃ c : ℤ, (2 : ℤ) • c = positiveTrace ℤ r (cartan ℤ r i)
  rw [positiveTrace_cartan]
  split_ifs
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- The terminal coroot has integral content two before any field base change. -/
theorem terminal_cartan_eq_two_smul (r : ℕ) :
    cartan ℤ (r + 1) (Fin.last r) = (2 : ℤ) •
      (Matrix.single (pos (r + 1) (Fin.last r)) (pos (r + 1) (Fin.last r)) 1 -
        Matrix.single (neg (r + 1) (Fin.last r)) (neg (r + 1) (Fin.last r)) 1) := by
  have h : ¬ (Fin.last r).val + 1 < r + 1 := by simp only [Fin.val_last]; omega
  rw [cartan_eq, dif_neg h]
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]

/-- In particular, do not apply the primitive-full-matrix-coordinate split
criterion to the B simple-coroot family. The needed parity correction is real. -/
theorem no_terminal_integral_coordinate (r : ℕ) :
    ¬ ∃ c : Mat ℤ (r + 1) →ₗ[ℤ] ℤ,
      c (cartan ℤ (r + 1) (Fin.last r)) = 1 := by
  rintro ⟨c, hc⟩
  rw [terminal_cartan_eq_two_smul, map_smul] at hc
  change (2 : ℤ) * c _ = 1 at hc
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntegralParityCoordinates
