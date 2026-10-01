import SymmetricSubgroupAsymptotics.MarkedC4QuotientProfiles
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The complete abelian Hall count

For a finite commutative group `T` of exponent dividing `2^N` and any finite
group `E`,

`∑_{K ≤ T} |Hom(E, T/K)| ≤ (∏_{k<N} (colₖ T + 1)) · 4^N · 2^(∑_{k<N} Ψ(colₖ T, colₖ E^ab))`,

where `Ψ(v, x) = max_{0 ≤ y ≤ v} y (v - y + x)`, explicitly `v x` if `v ≤ x`
and `(v+x)²/4` otherwise.  Every homomorphism to an abelian group factors
through the abelianization, and each quotient column profile is counted by
the Birkhoff-type bound with its homomorphism factor inside the same profile.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u

/-! ## The function `Ψ` -/

/-- `Ψ(v, x) = max_{0≤y≤v} y (v - y + x)`. -/
def psi (v x : ℝ) : ℝ := if v ≤ x then v * x else (v + x) ^ 2 / 4

theorem le_psi {v x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyv : y ≤ v) :
    y * (v - y + x) ≤ psi v x := by
  unfold psi
  split_ifs with h
  · nlinarith [mul_nonneg hy (sub_nonneg.mpr hyv), sub_nonneg.mpr h]
  · nlinarith [sq_nonneg (2 * y - v - x)]

theorem psi_nonneg {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) : 0 ≤ psi v x := by
  have := le_psi (v := v) (x := x) (y := 0) hx le_rfl hv
  simpa using this

/-! ## Homomorphisms to quotients -/

instance abelianization_finite (E : Type u) [Group E] [Finite E] :
    Finite (Abelianization E) :=
  Finite.of_surjective _ (QuotientGroup.mk_surjective (s := commutator E))

/-- A homomorphism from any group to a commutative group factors through the
abelianization. -/
def homAbelianizationEquiv (E : Type u) [Group E] (B : Type u) [CommGroup B] :
    (E →* B) ≃ (Abelianization E →* B) :=
  Abelianization.lift

theorem card_hom_quotient_le (N : ℕ) {T : Type u} [CommGroup T] [Finite T] (hT : HasExp2 T N)
    (E : Type u) [Group E] [Finite E] (K : Subgroup T) :
    Nat.card (E →* T ⧸ K) ≤
      2 ^ (∑ k ∈ Finset.range N, col (Abelianization E) k * col (T ⧸ K) k) := by
  rw [Nat.card_congr (homAbelianizationEquiv E (T ⧸ K))]
  apply card_hom_le
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_pow, hT x, QuotientGroup.mk_one]

/-! ## The Hall count -/

/-- **The complete abelian Hall count.** -/
theorem sum_card_hom_quotient_le (N : ℕ) (T : Type u) [CommGroup T] [Finite T]
    [Fintype (Subgroup T)]
    (hT : HasExp2 T N) (E : Type u) [Group E] [Finite E] :
    ((∑ K : Subgroup T, Nat.card (E →* T ⧸ K) : ℕ) : ℝ) ≤
      (∏ k ∈ Finset.range N, ((col T k : ℝ) + 1)) * 4 ^ N *
        (2 : ℝ) ^ (∑ k ∈ Finset.range N, psi (col T k) (col (Abelianization E) k)) := by
  set x : ℕ → ℕ := fun k => col (Abelianization E) k
  set t : ℕ → ℕ := fun k => col T k
  -- profiles as functions on `Fin N`
  let P : Finset (Fin N → ℕ) := Fintype.piFinset (fun k : Fin N => Finset.range (t k + 1))
  let prof : Subgroup T → (Fin N → ℕ) := fun K k => col (T ⧸ K) k
  have hmaps : ∀ K ∈ (Finset.univ : Finset (Subgroup T)), prof K ∈ P := by
    intro K _
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (col_quotient_le k K)
  -- each profile class
  have hclass : ∀ y ∈ P, ((∑ K ∈ Finset.univ.filter (fun K => prof K = y),
      Nat.card (E →* T ⧸ K) : ℕ) : ℝ) ≤ 4 ^ N *
        (2 : ℝ) ^ (∑ k ∈ Finset.range N, psi (t k) (x k)) := by
    intro y hy
    let y' : ℕ → ℕ := fun k => if h : k < N then y ⟨k, h⟩ else 0
    have hyle : ∀ k < N, y' k ≤ t k := by
      intro k hk
      have := (Fintype.mem_piFinset.mp hy) ⟨k, hk⟩
      rw [Finset.mem_range] at this
      simp only [y', dif_pos hk]
      exact Nat.lt_succ_iff.mp this
    -- the number of subgroups in the class
    have hcount : (Finset.univ.filter (fun K => prof K = y)).card ≤
        2 ^ (∑ k ∈ Finset.range N, (y' k * (t k - y' k) + 2)) := by
      have h := card_profileSet_le N T hT y'
      refine le_trans ?_ h
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_le_card_of_injective
        (fun K => (⟨K.1, fun k hk => by
          have := (Finset.mem_filter.mp K.2).2
          have h2 := congrFun this ⟨k, hk⟩
          simp only [prof] at h2
          simp only [y', dif_pos hk]
          exact h2⟩ : ProfileSet T N y')) ?_
      intro K₁ K₂ h
      exact Subtype.ext (congrArg (fun z : ProfileSet T N y' => z.1) h)
    -- each term
    have hterm : ∀ K ∈ Finset.univ.filter (fun K => prof K = y),
        Nat.card (E →* T ⧸ K) ≤ 2 ^ (∑ k ∈ Finset.range N, x k * y' k) := by
      intro K hK
      have h := card_hom_quotient_le N hT E K
      refine le_trans h (le_of_eq ?_)
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have := congrFun (Finset.mem_filter.mp hK).2 ⟨k, hk⟩
      simp only [prof] at this
      simp only [y', dif_pos hk, x, this]
    have hsum : (∑ K ∈ Finset.univ.filter (fun K => prof K = y),
        Nat.card (E →* T ⧸ K) : ℕ) ≤
        2 ^ (∑ k ∈ Finset.range N, (y' k * (t k - y' k) + 2)) *
          2 ^ (∑ k ∈ Finset.range N, x k * y' k) := by
      calc (∑ K ∈ Finset.univ.filter (fun K => prof K = y), Nat.card (E →* T ⧸ K) : ℕ)
          ≤ ∑ _K ∈ Finset.univ.filter (fun K => prof K = y),
              2 ^ (∑ k ∈ Finset.range N, x k * y' k) := Finset.sum_le_sum hterm
        _ = (Finset.univ.filter (fun K => prof K = y)).card *
              2 ^ (∑ k ∈ Finset.range N, x k * y' k) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ hcount
    -- the exponent
    have hexp : ((∑ k ∈ Finset.range N, (y' k * (t k - y' k) + 2) +
        ∑ k ∈ Finset.range N, x k * y' k : ℕ) : ℝ) ≤
        2 * N + ∑ k ∈ Finset.range N, psi (t k) (x k) := by
      push_cast
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      have : ∀ k ∈ Finset.range N, ((y' k : ℝ) * ((t k - y' k : ℕ) : ℝ) + (x k : ℝ) * y' k) ≤
          psi (t k) (x k) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [Nat.cast_sub (hyle k hk)]
        have := le_psi (v := t k) (x := x k) (y := y' k) (Nat.cast_nonneg _)
          (Nat.cast_nonneg _) (by exact_mod_cast hyle k hk)
        linarith
      have h2 := Finset.sum_le_sum this
      rw [Finset.sum_add_distrib] at h2
      simp only [nsmul_eq_mul]
      linarith
    calc ((∑ K ∈ Finset.univ.filter (fun K => prof K = y), Nat.card (E →* T ⧸ K) : ℕ) : ℝ)
        ≤ ((2 ^ (∑ k ∈ Finset.range N, (y' k * (t k - y' k) + 2)) *
            2 ^ (∑ k ∈ Finset.range N, x k * y' k) : ℕ) : ℝ) := by exact_mod_cast hsum
      _ = (2 : ℝ) ^ ((∑ k ∈ Finset.range N, (y' k * (t k - y' k) + 2) +
            ∑ k ∈ Finset.range N, x k * y' k : ℕ) : ℝ) := by
          rw [← pow_add, Real.rpow_natCast]
          push_cast
          ring
      _ ≤ (2 : ℝ) ^ (2 * (N : ℝ) + ∑ k ∈ Finset.range N, psi (t k) (x k)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 4 ^ N * (2 : ℝ) ^ (∑ k ∈ Finset.range N, psi (t k) (x k)) := by
          rw [Real.rpow_add (by norm_num), show (2 : ℝ) * N = ((2 * N : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast, pow_mul]
          norm_num
  -- sum over profiles
  have hP : (P.card : ℝ) = ∏ k ∈ Finset.range N, ((col T k : ℝ) + 1) := by
    simp only [P, Fintype.card_piFinset, Finset.card_range]
    push_cast
    rw [Finset.prod_range (fun k => (t k : ℝ) + 1)]
  calc ((∑ K : Subgroup T, Nat.card (E →* T ⧸ K) : ℕ) : ℝ)
      = ((∑ y ∈ P, ∑ K ∈ Finset.univ.filter (fun K => prof K = y),
          Nat.card (E →* T ⧸ K) : ℕ) : ℝ) := by
        rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ y ∈ P, ((∑ K ∈ Finset.univ.filter (fun K => prof K = y),
          Nat.card (E →* T ⧸ K) : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _y ∈ P, 4 ^ N * (2 : ℝ) ^ (∑ k ∈ Finset.range N, psi (t k) (x k)) :=
        Finset.sum_le_sum hclass
    _ = (∏ k ∈ Finset.range N, ((col T k : ℝ) + 1)) * 4 ^ N *
          (2 : ℝ) ^ (∑ k ∈ Finset.range N, psi (col T k) (col (Abelianization E) k)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hP]
        ring

end MarkedC4
end SymmetricSubgroupAsymptotics
