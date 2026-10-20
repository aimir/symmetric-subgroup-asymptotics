import SymmetricSubgroupAsymptotics.SymmetricUnimodalLayerCake

/-! Exact one-chain replacement in normalized middle-layer counting.
The two central ranks are paired to handle both parities uniformly. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

/-- The contribution of one symmetric chain [a,K-a] to the two central
ranks after adjoining a chain with total rank m. -/
def middlePairWeight (K a m i : ℕ) : ℕ :=
  (if i+a≤(K+m)/2 ∧ (K+m)/2+a≤i+K then 1 else 0)+
  (if i+a≤K+m-(K+m)/2 ∧ K+m-(K+m)/2+a≤i+K then 1 else 0)

theorem middlePairWeight_symmetricUnimodal (K a m : ℕ) (ha : 2*a≤K) :
    SymmetricUnimodal m (middlePairWeight K a m) := by
  constructor
  · intro i hi
    simp only [middlePairWeight]
    split_ifs <;> omega
  · intro i j hij hj
    simp only [middlePairWeight]
    split_ifs <;> omega

/-- Summing genuine symmetric-chain contributions preserves the exact
centered weight needed in the one-factor comparison. -/
theorem middlePairWeight_sum_symmetricUnimodal {C : Type} [Fintype C]
    (K m : ℕ) (start : C → ℕ) (hstart : ∀ c, 2*start c≤K) :
    SymmetricUnimodal m (fun i => ∑ c, middlePairWeight K (start c) m i) := by
  constructor
  · intro i hi
    exact Finset.sum_congr rfl (fun c _ =>
      (middlePairWeight_symmetricUnimodal K (start c) m (hstart c)).symmetric i hi)
  · intro i j hij hj
    exact Finset.sum_le_sum (fun c _ =>
      (middlePairWeight_symmetricUnimodal K (start c) m (hstart c)).monotone_left i j hij hj)

/-- Replacing one uniform chain of length m+1 by m independent Boolean
coordinates can only increase normalized middle mass. This integral
inequality is exact, not a Gaussian estimate. -/
theorem middle_pair_binomial_replacement {C : Type} [Fintype C]
    (K m : ℕ) (start : C → ℕ) (hstart : ∀ c, 2*start c≤K) :
    2^m*(∑ i : Fin (m+1), ∑ c, middlePairWeight K (start c) m i.val)≤
      (m+1)*(∑ i : Fin (m+1),
        (∑ c,middlePairWeight K (start c) m i.val)*m.choose i.val) := by
  have hw := middlePairWeight_sum_symmetricUnimodal K m start hstart
  have hmass (a : ℕ) :
      2^m*(∑ _i∈CentralBinomialPeakedness.centralSlice m a, (1 : ℕ))≤
        (m+1)*(∑ i∈CentralBinomialPeakedness.centralSlice m a,m.choose i.val) := by
    simpa only [Finset.sum_const,smul_eq_mul,mul_one,Nat.mul_comm] using
      CentralBinomialPeakedness.centralSlice_mass m a
  simpa only [mul_one] using hw.weighted_mass_le
    (fun _ : Fin (m+1) => 1) (fun i : Fin (m+1) => m.choose i.val) (2^m) (m+1) hmass

end SymmetricSubgroupAsymptotics
