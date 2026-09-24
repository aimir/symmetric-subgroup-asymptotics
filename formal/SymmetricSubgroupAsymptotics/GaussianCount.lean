import SymmetricSubgroupAsymptotics.Foundations

/-!
# Counting binary subspaces by dimension

We count independent ordered tuples in two ways: directly, and by their span.
The fibre over a k-dimensional subspace consists of its ordered bases. Summing
these dimension counts identifies the explicit Gaussian sum with the actual
number of subspaces.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private abbrev BinarySpace (r : ℕ) := Fin r → ZMod 2

private abbrev BinaryFrame (r k : ℕ) :=
  { v : Fin k → BinarySpace r // LinearIndependent (ZMod 2) v }

private def frameSpan {r k : ℕ} (v : BinaryFrame r k) :
    Submodule (ZMod 2) (BinarySpace r) := Submodule.span (ZMod 2) (Set.range v.1)

private theorem frameSpan_finrank {r k : ℕ} (v : BinaryFrame r k) :
    Module.finrank (ZMod 2) (frameSpan v) = k := by
  simpa [frameSpan] using finrank_span_eq_card v.2

private theorem span_inside_eq {r k : ℕ}
    (S : Submodule (ZMod 2) (BinarySpace r)) (hS : Module.finrank (ZMod 2) S = k)
    (v : Fin k → S) (hv : LinearIndependent (ZMod 2) v) :
    Submodule.span (ZMod 2) (Set.range (fun i ↦ (v i : BinarySpace r))) = S := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (v i).2
  · have hli := hv.map' S.subtype (by simp)
    have hrank := finrank_span_eq_card hli
    simpa [Function.comp_def, hS] using hrank

private def frameSpanFiberEquiv {r k : ℕ}
    (S : Submodule (ZMod 2) (BinarySpace r)) (hS : Module.finrank (ZMod 2) S = k) :
    {v : BinaryFrame r k // frameSpan v = S} ≃
      {v : Fin k → S // LinearIndependent (ZMod 2) v} where
  toFun v := ⟨fun i ↦ ⟨v.1.1 i, by
    exact (le_of_eq v.2) (Submodule.subset_span (Set.mem_range_self i))⟩,
    LinearIndependent.of_comp S.subtype v.1.2⟩
  invFun v := ⟨⟨fun i ↦ (v.1 i : BinarySpace r), v.2.map' S.subtype (by simp)⟩,
    span_inside_eq S hS v.1 v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem frame_fiber_card {r k : ℕ}
    (S : Submodule (ZMod 2) (BinarySpace r)) (hS : Module.finrank (ZMod 2) S = k) :
    Nat.card {v : BinaryFrame r k // frameSpan v = S} =
      ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  rw [Nat.card_congr (frameSpanFiberEquiv S hS), card_linearIndependent]
  · simp [hS]
  · omega

/-- Counting independent tuples by their unique span gives the fraction-free
Gaussian cardinality identity. -/
theorem binary_rank_count_mul (r k : ℕ) (hk : k ≤ r) :
    Nat.card { S : Submodule (ZMod 2) (BinarySpace r) //
        Module.finrank (ZMod 2) S = k } *
      (∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ))) =
        ∏ i : Fin k, (2 ^ r - 2 ^ (i : ℕ)) := by
  classical
  letI := Fintype.ofFinite { S : Submodule (ZMod 2) (BinarySpace r) //
    Module.finrank (ZMod 2) S = k }
  let e := Equiv.sigmaSubtypeFiberEquiv (frameSpan (r := r) (k := k))
    (fun S ↦ Module.finrank (ZMod 2) S = k) frameSpan_finrank
  have h := Nat.card_congr e
  rw [Nat.card_sigma] at h
  have hc : ∀ S : { S : Submodule (ZMod 2) (BinarySpace r) //
      Module.finrank (ZMod 2) S = k },
      Nat.card {v : BinaryFrame r k // frameSpan v = S.1} =
        ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) :=
    fun S ↦ frame_fiber_card S.1 S.2
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at h
  rw [h]
  simpa using card_linearIndependent (K := ZMod 2) (V := BinarySpace r)
    (k := k) (by simpa using hk)

private theorem nat_frame_product_cast (r k : ℕ) (hk : k ≤ r) :
    ((∏ i : Fin k, (2 ^ r - 2 ^ (i : ℕ)) : ℕ) : ℚ) =
      ∏ i : Fin k, ((2 : ℚ) ^ r - 2 ^ (i : ℕ)) := by
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_sub (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
    (le_trans i.isLt.le hk))]
  push_cast
  rfl

/-- There are exactly the Gaussian coefficient many k-dimensional binary
subspaces, as an equality of rational numbers. -/
theorem binary_rank_count_eq (r k : ℕ) (hk : k ≤ r) :
    (Nat.card { S : Submodule (ZMod 2) (BinarySpace r) //
        Module.finrank (ZMod 2) S = k } : ℚ) = binaryGaussianCoefficient r k := by
  have h := congrArg (fun n : ℕ ↦ (n : ℚ)) (binary_rank_count_mul r k hk)
  dsimp only at h
  rw [Nat.cast_mul, nat_frame_product_cast k k le_rfl,
    nat_frame_product_cast r k hk] at h
  have hden : (∏ i : Fin k, ((2 : ℚ) ^ k - 2 ^ (i : ℕ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (binaryGaussian_denominator_pos i.isLt)
  apply (eq_div_iff hden).mpr at h
  rw [h]
  unfold binaryGaussianCoefficient
  rw [← Finset.prod_div_distrib]
  exact Fin.prod_univ_eq_prod_range
    (fun i ↦ ((2 : ℚ) ^ r - 2 ^ i) / (2 ^ k - 2 ^ i)) k

private def subspaceRankIndex (r : ℕ) (S : Submodule (ZMod 2) (BinarySpace r)) :
    Fin (r + 1) :=
  ⟨Module.finrank (ZMod 2) S, Nat.lt_succ_of_le (by simpa using S.finrank_le)⟩

/-- The explicit finite Gaussian sum equals the cardinality of the actual
binary subspace type, without identifying or quotienting distinct subspaces. -/
theorem binarySubspaceCount_eq_gaussianSum (r : ℕ) :
    (binarySubspaceCount r : ℚ) = binaryGaussianSum r := by
  classical
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv (subspaceRankIndex r))
  rw [Nat.card_sigma] at h
  have hf (k : Fin (r + 1)) :
      Nat.card { S : Submodule (ZMod 2) (BinarySpace r) // subspaceRankIndex r S = k } =
        Nat.card { S : Submodule (ZMod 2) (BinarySpace r) //
          Module.finrank (ZMod 2) S = (k : ℕ) } := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro S
    exact Fin.ext_iff
  simp only [hf] at h
  have hc := congrArg (fun n : ℕ ↦ (n : ℚ)) h.symm
  dsimp only at hc
  rw [Nat.cast_sum] at hc
  calc
    (binarySubspaceCount r : ℚ) =
        ∑ k : Fin (r + 1), (Nat.card { S : Submodule (ZMod 2) (BinarySpace r) //
          Module.finrank (ZMod 2) S = (k : ℕ) } : ℚ) := hc
    _ = ∑ k : Fin (r + 1), binaryGaussianCoefficient r k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact binary_rank_count_eq r k (Nat.le_of_lt_succ k.isLt)
    _ = binaryGaussianSum r := by
      exact Fin.sum_univ_eq_sum_range _ _

end SymmetricSubgroupAsymptotics
