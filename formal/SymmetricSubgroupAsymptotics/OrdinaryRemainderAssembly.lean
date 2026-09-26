import SymmetricSubgroupAsymptotics.CriticalFamilyAsymptotic
import SymmetricSubgroupAsymptotics.Recurrence

/-! The literal noncritical complement among all subgroups of S_n, using
the complete critical family in both parities. Exact partition precedes
normalization. The final recurrence theorem retains its actual counting
and row estimates as explicit inputs; it assumes no bounded total count. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

/-- Forget only the critical-family property, retaining the actual subgroup
on Fin n. Both branches of CriticalSubgroups are literal subgroup subtypes. -/
def criticalSubgroupEmbedding (n : ℕ) :
    CriticalSubgroups n ↪ Subgroup (Equiv.Perm (Fin n)) := by
  unfold CriticalSubgroups
  split <;> exact ⟨Subtype.val, Subtype.val_injective⟩

/-- Membership in the entire critical family, including all full lifts and
the permitted odd marker. No binary or fixed-point-free restriction enters. -/
def IsCriticalSubgroup (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  H ∈ Set.range (criticalSubgroupEmbedding n)

abbrev OrdinaryRemainderSubgroups (n : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin n)) // ¬ IsCriticalSubgroup n H}

def criticalSubgroupsEquivLiteral (n : ℕ) :
    CriticalSubgroups n ≃ {H : Subgroup (Equiv.Perm (Fin n)) // IsCriticalSubgroup n H} :=
  Equiv.ofInjective (criticalSubgroupEmbedding n) (criticalSubgroupEmbedding n).injective

/-- Exact disjoint partition of every actual subgroup, not only 2-groups. -/
def ordinarySubgroupsPartitionEquiv (n : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) ≃ CriticalSubgroups n ⊕ OrdinaryRemainderSubgroups n :=
  (Equiv.sumCompl (IsCriticalSubgroup n)).symm.trans
    (Equiv.sumCongr (criticalSubgroupsEquivLiteral n).symm (Equiv.refl _))

@[simp] theorem ordinarySubgroupsPartitionEquiv_inl (n : ℕ) (H : CriticalSubgroups n) :
    (ordinarySubgroupsPartitionEquiv n).symm (Sum.inl H)=criticalSubgroupEmbedding n H := rfl

@[simp] theorem ordinarySubgroupsPartitionEquiv_inr (n : ℕ)
    (H : OrdinaryRemainderSubgroups n) :
    (ordinarySubgroupsPartitionEquiv n).symm (Sum.inr H)=H.1 := rfl

theorem ordinarySubgroups_card_partition (n : ℕ) :
    subgroupCount n=Nat.card (CriticalSubgroups n)+Nat.card (OrdinaryRemainderSubgroups n) := by
  unfold subgroupCount
  rw [Nat.card_congr (ordinarySubgroupsPartitionEquiv n), Nat.card_sum]

def ordinarySubgroupRatio (n : ℕ) : ℝ :=
  (subgroupCount n : ℝ) / exactBenchmark n

def ordinaryCriticalRatio (n : ℕ) : ℝ :=
  (Nat.card (CriticalSubgroups n) : ℝ) / exactBenchmark n

def ordinaryRemainderRatio (n : ℕ) : ℝ :=
  (Nat.card (OrdinaryRemainderSubgroups n) : ℝ) / exactBenchmark n

theorem ordinarySubgroupRatio_partition (n : ℕ) :
    ordinarySubgroupRatio n=ordinaryCriticalRatio n+ordinaryRemainderRatio n := by
  unfold ordinarySubgroupRatio ordinaryCriticalRatio ordinaryRemainderRatio
  rw [ordinarySubgroups_card_partition, Nat.cast_add, add_div]

theorem ordinarySubgroupRatio_nonneg (n : ℕ) : 0≤ordinarySubgroupRatio n :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos n).le

theorem ordinaryCriticalRatio_nonneg (n : ℕ) : 0≤ordinaryCriticalRatio n :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos n).le

theorem ordinaryRemainderRatio_nonneg (n : ℕ) : 0≤ordinaryRemainderRatio n :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos n).le

theorem ordinaryRemainderRatio_le_total (n : ℕ) :
    ordinaryRemainderRatio n≤ordinarySubgroupRatio n := by
  rw [ordinarySubgroupRatio_partition]
  exact le_add_of_nonneg_left (ordinaryCriticalRatio_nonneg n)

/-- Only the already proved complete critical count supplies this bound. -/
theorem ordinaryCriticalRatio_bounded :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ordinaryCriticalRatio n≤C :=
  criticalSubgroups_normalized_bounded

/-- An exponential estimate for the literal full complement gives T1,
uniformly across both parities. The complement estimate remains an input. -/
theorem T1_of_ordinaryRemainder_exponential {c K : ℝ} {N : ℕ}
    (hc : 0<c) (hK : 0<K)
    (hremainder : ∀ n, N≤n →
      ordinaryRemainderRatio n≤K*(2 : ℝ)^(-c*(n : ℝ))) : T1 := by
  obtain ⟨A,hA,NA,hNA,hcritical⟩ := criticalSubgroups_relative_error
  refine ⟨min c (1/96), A+K, lt_min hc (by norm_num), by positivity,
    max NA N, le_trans hNA (le_max_left _ _), ?_⟩
  intro n hn
  have hnA : NA≤n := (le_max_left NA N).trans hn
  have hnN : N≤n := (le_max_right NA N).trans hn
  have hcmin : min c (1/96)≤c := min_le_left _ _
  have hamin : min c (1/96)≤(1/96 : ℝ) := min_le_right _ _
  have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hpa : (2 : ℝ)^(-(n : ℝ)/96)≤(2 : ℝ)^(-min c (1/96)*(n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hpc : (2 : ℝ)^(-c*(n : ℝ))≤(2 : ℝ)^(-min c (1/96)*(n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  change |ordinarySubgroupRatio n-1|≤_
  calc
    |ordinarySubgroupRatio n-1|=
        |(ordinaryCriticalRatio n-1)+ordinaryRemainderRatio n| := by
      rw [ordinarySubgroupRatio_partition]
      congr 1
      ring
    _≤|ordinaryCriticalRatio n-1|+|ordinaryRemainderRatio n| := abs_add_le _ _
    _=|ordinaryCriticalRatio n-1|+ordinaryRemainderRatio n := by
      rw [abs_of_nonneg (ordinaryRemainderRatio_nonneg n)]
    _≤A*(2 : ℝ)^(-(n : ℝ)/96)+K*(2 : ℝ)^(-c*(n : ℝ)) :=
      add_le_add (hcritical n hnA) (hremainder n hnN)
    _≤A*(2 : ℝ)^(-min c (1/96)*(n : ℝ))+
        K*(2 : ℝ)^(-min c (1/96)*(n : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hpa hA.le)
        (mul_le_mul_of_nonneg_left hpc hK.le)
    _=(A+K)*(2 : ℝ)^(-min c (1/96)*(n : ℝ)) := by ring

/-- A genuine forward counting recurrence first bounds the complete total
sequence. The only forcing bound used is the proved critical-family bound
plus the displayed scalar estimate; total boundedness is a conclusion. -/
theorem ordinarySubgroupRatio_bounded_of_recurrence
    {scalar : ℕ → ℝ} {kernel : ℕ → ℕ → ℝ} {N : ℕ} {S q : ℝ}
    (hS : 0≤S) (hq : q<1)
    (hkernel : ∀ n, N≤n → ∀ m ∈ Finset.range n, 0≤kernel n m)
    (hscalar : ∀ n, N≤n → scalar n≤S)
    (hrow : ∀ n, N≤n → (∑ m ∈ Finset.range n, kernel n m)≤q)
    (hrecurrence : ∀ n, N≤n → ordinaryRemainderRatio n≤
      scalar n+∑ m ∈ Finset.range n, kernel n m*ordinarySubgroupRatio m) :
    ∃ M : ℝ, 0<M ∧ ∀ n, ordinarySubgroupRatio n≤M := by
  obtain ⟨C,hC,hcritical⟩ := ordinaryCriticalRatio_bounded
  apply bounded_of_eventual_row_contraction
    (a := ordinarySubgroupRatio) (forcing := fun n => ordinaryCriticalRatio n+scalar n)
    (N := N) (B := C+S) (q := q) ordinarySubgroupRatio_nonneg
    (by linarith) hq hkernel
  · intro n hn
    exact add_le_add (hcritical n) (hscalar n hn)
  · exact hrow
  · intro n hn
    rw [ordinarySubgroupRatio_partition]
    linarith [hrecurrence n hn]

/-- Conditional ordinary-count assembly. The actual counting recurrence and
exponential row/scalar estimates remain inputs for the literal complement of
the complete critical family. Exponential row decay supplies eventual
contraction, which first proves boundedness of the complete total count. -/
theorem T1_of_ordinaryRemainder_recurrence
    {scalar : ℕ → ℝ} {kernel : ℕ → ℕ → ℝ} {N : ℕ} {c Cs Ck : ℝ}
    (hc : 0<c) (hCs : 0<Cs) (hCk : 0≤Ck)
    (hkernel : ∀ n, N≤n → ∀ m ∈ Finset.range n, 0≤kernel n m)
    (hrecurrence : ∀ n, N≤n → ordinaryRemainderRatio n≤
      scalar n+∑ m ∈ Finset.range n, kernel n m*ordinarySubgroupRatio m)
    (hscalar : ∀ n, N≤n → scalar n≤Cs*(2 : ℝ)^(-c*(n : ℝ)))
    (hrow : ∀ n, N≤n →
      (∑ m ∈ Finset.range n, kernel n m)≤Ck*(2 : ℝ)^(-c*(n : ℝ))) : T1 := by
  have hscalarBound : ∀ n, N≤n → scalar n≤Cs := by
    intro n hn
    have hp : (2 : ℝ)^(-c*(n : ℝ))≤1 := by
      have he : -c*(n : ℝ)≤0 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) he
    exact (hscalar n hn).trans ((mul_le_mul_of_nonneg_left hp hCs.le).trans_eq (mul_one Cs))
  obtain ⟨NE,hdecay⟩ :=
    Filter.eventually_atTop.mp (eventually_exponential_le_inv_rpow hc 1)
  let NC : ℕ := max N (max NE (max 1 ⌈2*Ck⌉₊))
  have hN : N≤NC := le_max_left _ _
  have hNE : NE≤NC := (le_max_left NE _).trans (le_max_right N _)
  have hlarge : max 1 ⌈2*Ck⌉₊≤NC :=
    (le_max_right NE _).trans (le_max_right N _)
  have hcontract : ∀ n, NC≤n → (∑ m ∈ Finset.range n, kernel n m)≤(1/2 : ℝ) := by
    intro n hn
    have hnlarge := hlarge.trans hn
    have hn1 : 1≤n := (le_max_left _ _).trans hnlarge
    have hnpos : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hnC : 2*Ck≤(n : ℝ) := (Nat.le_ceil (2*Ck)).trans
      (by exact_mod_cast (le_max_right _ _).trans hnlarge)
    have he := hdecay n (hNE.trans hn)
    rw [Real.rpow_one] at he
    apply (hrow n (hN.trans hn)).trans
      ((mul_le_mul_of_nonneg_left he hCk).trans ?_)
    rw [mul_one_div]
    exact (div_le_iff₀ hnpos).mpr (by linarith)
  have hbounded := ordinarySubgroupRatio_bounded_of_recurrence
    (N := NC) (q := (1/2 : ℝ)) hCs.le (by norm_num)
    (fun n hn => hkernel n (hN.trans hn))
    (fun n hn => hscalarBound n (hN.trans hn)) hcontract
    (fun n hn => hrecurrence n (hN.trans hn))
  obtain ⟨c',K,hc',hK,herror⟩ := exponential_error_of_bounded_targets
    hc hCs hCk hbounded hkernel hrecurrence hscalar hrow
  exact T1_of_ordinaryRemainder_exponential hc' hK herror

end SymmetricSubgroupAsymptotics
