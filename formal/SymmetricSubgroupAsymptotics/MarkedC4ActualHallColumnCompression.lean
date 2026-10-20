import SymmetricSubgroupAsymptotics.MarkedC4HallSpliceCount
import SymmetricSubgroupAsymptotics.MarkedC4ColumnCompression

/-! The genuine Hall-fibre estimate for arbitrary abelian physical factors.
No elementary-exponent assumption is imposed on A. Its total column mass is
DERIVED from its actual order, and the two literal C4 mark columns remain
separate. This is the missing general scope before actual Case-I coding. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHallColumnCompression

theorem card_eq_two_pow_column_sum : ∀ (N : ℕ) (A : Type) [CommGroup A] [Finite A],
    HasExp2 A N → Nat.card A=2^(∑ k ∈ Finset.range N,col A k)
  | 0,A,_,_,hA => by
    letI := subsingleton_of_hasExp2_zero hA
    simp only [Finset.range_zero,Finset.sum_empty,pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
  | N+1,A,_,_,hA => by
    rw [card_eq_two_pow_col_mul A,
      card_eq_two_pow_column_sum N (sqs A) (hasExp2_sqs hA)]
    have hs : (∑ k ∈ Finset.range (N+1),col A k)=
        col A 0+∑ k ∈ Finset.range N,col (sqs A) k := by
      rw [Finset.sum_range_succ']
      simp only [col_succ]
      ring
    rw [hs,pow_add]

theorem col_antitone (A : Type) [CommGroup A] [Finite A] : Antitone (col A) :=
  antitone_nat_of_succ_le (col_succ_le A)

/-- The physical cardinality bound supplies the complete column budget. -/
theorem column_mass_le (N : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A N) {a : ℝ} (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2)) :
    (∑ k ∈ Finset.range N,(col A k : ℝ))≤a/2 := by
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ)<2)).mp
  have he := card_eq_two_pow_column_sum N A hA
  rw [he] at hcard
  have hc : ((∑ k ∈ Finset.range N,col A k : ℕ) : ℝ)=
      ∑ k ∈ Finset.range N,(col A k : ℝ) := by simp
  rw [← hc,Real.rpow_natCast]
  exact_mod_cast hcard

/-- All physical abelian columns are paid jointly, while the actual first
TWO source columns are preserved rather than independently maximized. -/
theorem exponent_le (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m)) (E : Type) [Group E] [Finite E]
    {a : ℝ} (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2)) :
    (∑ k ∈ Finset.range (2+m),
      psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
        (col (Abelianization E) k)) ≤
      psi (a/2+r) (col (Abelianization E) 0)+psi r (col (Abelianization E) 1) := by
  have hmass := column_mass_le (2+m) A hA hcard
  have hmass' : (col A 0 : ℝ)+col A 1+
      ∑ k ∈ Finset.range m,(col A (k+2) : ℝ)≤a/2 := by
    rw [Finset.sum_range_add] at hmass
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceAdd,Nat.add_comm] using hmass
  have hcomp := psi_twoColumn_packet_compression (Finset.range m)
    (fun k => (col A (k+2) : ℝ)) (fun k => (col (Abelianization E) (k+2) : ℝ))
    (a := a) (a₀ := col A 0) (a₁ := col A 1) (r := r)
    (x₀ := col (Abelianization E) 0) (x₁ := col (Abelianization E) 1)
    (by positivity) (by positivity) (by exact_mod_cast col_succ_le A 0)
    (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast col_succ_le (Abelianization E) 0)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun k _ => by
      change (col (Abelianization E) (k+2) : ℝ)≤(col (Abelianization E) 0 : ℝ)
      exact Nat.cast_le.mpr (col_antitone (Abelianization E) (show 0≤k+2 by omega)))
    hmass'
  rw [Finset.sum_range_add]
  have htail (k : ℕ) : col (A × Multiplicative (Fin r → ZMod 4)) (2+k)=col A (k+2) := by
    rw [col_prod_cyclicFourCoordinates,if_neg (by omega)]
    simp only [add_zero,Nat.add_comm]
  simp_rw [htail]
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    col_prod_cyclicFourCoordinates,Nat.reduceLT,if_true,Nat.cast_add,Nat.add_comm,add_comm] using hcomp

/-- Exact actual Hall fibre, with the complete prefactor retained. Its
constant column depth is paid by the subsequent fixed-cutoff polynomial. -/
theorem fullSecond_le (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    [Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4)))]
    (hA : HasExp2 A (2+m)) (E : Type) [Group E] [Finite E]
    {a : ℝ} (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2)) :
    (Nat.card (AbelianProductGraphClassification.FullSecond
      (A × Multiplicative (Fin r → ZMod 4)) E) : ℝ) ≤
      (∏ k ∈ Finset.range (2+m),
        ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m)*
      (2 : ℝ)^(psi (a/2+r) (col (Abelianization E) 0)+
        psi r (col (Abelianization E) 1)) := by
  have h := cyclicFourFullSecond_le (2+m) r A hA (by omega) E
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (exponent_le m r A hA E hcard))
    (by positivity))

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHallColumnCompression
