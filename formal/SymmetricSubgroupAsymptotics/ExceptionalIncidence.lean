import SymmetricSubgroupAsymptotics.QuadraticSubspaceIncidence
import SymmetricSubgroupAsymptotics.ExceptionalGaussianBound
import SymmetricSubgroupAsymptotics.BinaryRankSums

/-!
# Weighted exceptional incidences of actual subspaces

Every actual image subspace and every nonzero actual relation subspace is
retained, with its exact lift weight. Grouping by their ranks is an equality;
only afterwards are the proved joint incidence bounds applied.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Finite W]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)]

/-- Literal weighted incidences over actual subspaces. The zero relation
subspace is excluded, leaving the positive-relation part of the lift weight. -/
def exceptionalQuadraticIncidence {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) : ℝ :=
  ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // B ≠ ⊥},
    ∑ U : Submodule (ZMod 2) (Fin R → ZMod 2),
      if FullQuadraticSubspace e B.1 q U then
        (2 : ℝ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.1) else 0

/-- An exact rank-binned expression, still counting every actual retained
relation subspace separately. -/
def exceptionalQuadraticIncidenceByRank {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) : ℝ :=
  ∑ k ∈ Finset.range (R + 1), ∑ l ∈ Finset.Icc 1 (Fintype.card ι),
    ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // Module.finrank (ZMod 2) B = l},
      (Nat.card {U : Submodule (ZMod 2) (Fin R → ZMod 2) //
        Module.finrank (ZMod 2) U = k ∧ FullQuadraticSubspace e B.1 q U} : ℝ) *
        (2 : ℝ) ^ (k * l)

private theorem sum_indicator_constant {A : Type*} [Fintype A]
    (p : A → Prop) (c : ℝ) :
    (∑ a, if p a then c else 0) = (Nat.card {a // p a} : ℝ) * c := by
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [FiniteDimensional (ZMod 2) W] [Finite W]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)] in
private theorem quadratic_rank_weight {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (B : Submodule (ZMod 2) (ι → ZMod 2)) (k : ℕ) :
    (∑ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // Module.finrank (ZMod 2) U = k},
      if FullQuadraticSubspace e B q U.1 then
        (2 : ℝ) ^ (Module.finrank (ZMod 2) U.1 * Module.finrank (ZMod 2) B) else 0) =
      (Nat.card {U : Submodule (ZMod 2) (Fin R → ZMod 2) //
        Module.finrank (ZMod 2) U = k ∧ FullQuadraticSubspace e B q U} : ℝ) *
        (2 : ℝ) ^ (k * Module.finrank (ZMod 2) B) := by
  calc
    _ = ∑ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // Module.finrank (ZMod 2) U = k},
        if FullQuadraticSubspace e B q U.1 then
          (2 : ℝ) ^ (k * Module.finrank (ZMod 2) B) else 0 := by
      apply Finset.sum_congr rfl
      intro U _
      rw [U.2]
    _ = _ := by
      rw [sum_indicator_constant]
      rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun U : Submodule (ZMod 2) (Fin R → ZMod 2) => Module.finrank (ZMod 2) U = k)
        (FullQuadraticSubspace e B q))]

omit [FiniteDimensional (ZMod 2) W] [Finite W]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)] in
/-- No subspace or weight is lost when passing to the rank-binned expression. -/
theorem exceptionalQuadraticIncidence_eq_byRank {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :
    exceptionalQuadraticIncidence e q = exceptionalQuadraticIncidenceByRank e q := by
  unfold exceptionalQuadraticIncidence exceptionalQuadraticIncidenceByRank
  rw [binary_nonzero_subspace_sum_by_rank (fun B =>
    ∑ U : Submodule (ZMod 2) (Fin R → ZMod 2),
      if FullQuadraticSubspace e B q U then
        (2 : ℝ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B) else 0)]
  simp only [Module.finrank_pi]
  calc
    _ = ∑ l ∈ Finset.Icc 1 (Fintype.card ι),
        ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // Module.finrank (ZMod 2) B = l},
        ∑ k ∈ Finset.range (R + 1),
          (Nat.card {U : Submodule (ZMod 2) (Fin R → ZMod 2) //
            Module.finrank (ZMod 2) U = k ∧ FullQuadraticSubspace e B.1 q U} : ℝ) *
            (2 : ℝ) ^ (k * l) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro B _
      rw [binary_subspace_sum_by_rank]
      simp only [Module.finrank_pi, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro k _
      simpa only [B.2] using quadratic_rank_weight e q B.1 k
    _ = ∑ l ∈ Finset.Icc 1 (Fintype.card ι), ∑ k ∈ Finset.range (R + 1),
        ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // Module.finrank (ZMod 2) B = l},
          (Nat.card {U : Submodule (ZMod 2) (Fin R → ZMod 2) //
            Module.finrank (ZMod 2) U = k ∧ FullQuadraticSubspace e B.1 q U} : ℝ) *
            (2 : ℝ) ^ (k * l) := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem exceptional_rank_term_le {R k l : ℕ} (hk : k ≤ R)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ 72)
    (B : {B : Submodule (ZMod 2) (ι → ZMod 2) // Module.finrank (ZMod 2) B = l}) :
    (Nat.card {U : Submodule (ZMod 2) (Fin R → ZMod 2) //
      Module.finrank (ZMod 2) U = k ∧ FullQuadraticSubspace e B.1 q U} : ℝ) *
      (2 : ℝ) ^ (k * l) ≤
      eulerProduct⁻¹ * (binaryGaussianCoefficient R k : ℝ) * (72 : ℝ)^l /
        (2 : ℝ)^(k*l) := by
  have h := fullQuadraticSubspace_count_le hk e B.1 q hq hv 72 hM
  rw [B.2] at h
  calc
    _ ≤ (eulerProduct⁻¹ * (binaryGaussianCoefficient R k : ℝ) * (72 : ℝ)^l /
        (2 : ℝ)^(2*k*l)) * (2 : ℝ)^(k*l) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by
      have hp : (2 : ℝ)^(2*k*l) = (2 : ℝ)^(k*l) * (2 : ℝ)^(k*l) := by
        rw [← pow_add]
        congr 1
        ring
      rw [hp]
      have hn : (2 : ℝ)^(k*l) ≠ 0 := by positivity
      field_simp

/-- The actual weighted incidence sum is dominated by the complete numerical
Gaussian sum. The remaining Euler factor comes from ordered-injection loss. -/
theorem exceptionalQuadraticIncidence_le_gaussian {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ 72) :
    exceptionalQuadraticIncidence e q ≤
      eulerProduct⁻¹ * exceptionalGaussianSum R (Fintype.card ι) := by
  rw [exceptionalQuadraticIncidence_eq_byRank]
  unfold exceptionalQuadraticIncidenceByRank exceptionalGaussianSum
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  calc
    _ ≤ ∑ _B : {B : Submodule (ZMod 2) (ι → ZMod 2) // Module.finrank (ZMod 2) B = l},
        eulerProduct⁻¹ * (binaryGaussianCoefficient R k : ℝ) * (72 : ℝ)^l /
          (2 : ℝ)^(k*l) :=
      Finset.sum_le_sum (fun B _ => exceptional_rank_term_le (by simpa using hk) e q hq hv hM B)
    _ = _ := by
      have hc := binary_subspace_rank_card (V := ι → ZMod 2) l
        (by simpa only [Module.finrank_pi] using (Finset.mem_Icc.mp hl).2)
      simp only [Module.finrank_pi] at hc
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]
      ring

omit [Finite W] [∀ i, Finite (V i)] in
/-- The chart and the two-dimensional pivot minimum imply a nonnegative
profile deficit; it is proved here rather than postulated. -/
theorem quadratic_profile_gap_nonneg {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i)) :
    0 ≤ (R : ℝ) / 2 - Fintype.card ι := by
  have he : Module.finrank (ZMod 2) W + ∑ i, Module.finrank (ZMod 2) (V i) = R := by
    simpa only [Module.finrank_pi, Fintype.card_fin, Module.finrank_prod,
      Module.finrank_pi_fintype] using e.finrank_eq.symm
  have hs : 2 * Fintype.card ι ≤ ∑ i, Module.finrank (ZMod 2) (V i) := by
    calc
      _ = ∑ _i : ι, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hv i)
  have hh : 2 * Fintype.card ι ≤ R := by omega
  have hh' : (2 : ℝ) * Fintype.card ι ≤ R := by exact_mod_cast hh
  linarith

/-- Uniform Gaussian-relative exceptional incidence bound, including zero
deficit and all parity classes of the total dimension. -/
theorem exceptionalQuadraticIncidence_le {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ 72) :
    exceptionalQuadraticIncidence e q ≤
      (exceptionalGaussianConstant / eulerProduct) * (binaryGaussianSum R : ℝ) *
        (2 : ℝ)^(-((R : ℝ)/2 - Fintype.card ι)) := by
  calc
    _ ≤ eulerProduct⁻¹ * exceptionalGaussianSum R (Fintype.card ι) :=
      exceptionalQuadraticIncidence_le_gaussian e q hq hv hM
    _ ≤ eulerProduct⁻¹ * (exceptionalGaussianConstant * (binaryGaussianSum R : ℝ) *
        (2 : ℝ)^(-((R : ℝ)/2 - Fintype.card ι))) :=
      mul_le_mul_of_nonneg_left (exceptionalGaussianSum_le R (Fintype.card ι)
        (quadratic_profile_gap_nonneg e hv)) (inv_nonneg.mpr euler_positive.le)
    _ = _ := by ring

end SymmetricSubgroupAsymptotics
