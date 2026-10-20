import SymmetricSubgroupAsymptotics.FiniteSymmetricChainRankCount
import SymmetricSubgroupAsymptotics.FiniteSymmetricChainPairProduct
import SymmetricSubgroupAsymptotics.BinaryGridRankCount

/-! Replacing an actual uniform-chain factor by a Boolean grid increases
normalized middle mass.  Both sides count original product points. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteSymmetricChains

variable {I : Type} [Preorder I] [Fintype I] {rank : I → ℕ} {K : ℕ}
    (D : FiniteSymmetricChains I rank K) [Fintype D.Colour]

theorem product_rank_card_right {J : Type} [Fintype J] (rJ : J → ℕ) (t : ℕ) :
    (Finset.univ.filter (fun a : I×J => rank a.1+rJ a.2=t)).card =
      ∑ y : J, ∑ c : D.Colour,
        if rJ y+D.start c≤t ∧ t+D.start c≤rJ y+K then 1 else 0 := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hit : rJ y≤t
  · have hr : (∑ x : I, if rank x+rJ y=t then 1 else 0) =
        (Finset.univ.filter (fun x : I => rank x=t-rJ y)).card := by
      rw [Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      have he : (rank x+rJ y=t) ↔ (rank x=t-rJ y) := by omega
      simp only [he]
    rw [hr,D.rank_card (t-rJ y)]
    apply Finset.sum_congr rfl
    intro c _
    have he : (D.start c≤t-rJ y ∧ t-rJ y+D.start c≤K) ↔
        (rJ y+D.start c≤t ∧ t+D.start c≤rJ y+K) := by omega
    simp only [he]
  · have hleft : (∑ x : I, if rank x+rJ y=t then 1 else 0)=0 := by
      apply Finset.sum_eq_zero
      intro x _
      exact if_neg (by omega)
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro c _
    exact if_neg (by omega)

include D in
/-- The exact one-factor comparison for the original product middle
layers.  It makes no estimate of a Gaussian or asymptotic width. -/
theorem middle_card_chain_le_binary (m : ℕ) :
    2^m*(Finset.univ.filter (fun a : I×Fin (m+1) =>
        rank a.1+a.2.val=(K+m)/2)).card ≤
      (m+1)*(Finset.univ.filter (fun a : I×PrimeCosetGrid 2 m =>
        rank a.1+primeGridRank 2 m a.2=(K+m)/2)).card := by
  let A := (Finset.univ.filter (fun a : I×Fin (m+1) =>
    rank a.1+a.2.val=(K+m)/2)).card
  let B := (Finset.univ.filter (fun a : I×PrimeCosetGrid 2 m =>
    rank a.1+primeGridRank 2 m a.2=(K+m)/2)).card
  have DA : FiniteSymmetricChains (I×Fin (m+1))
      (fun a => rank a.1+a.2.val) (K+m) := by
    have h := D.product (m+1) (by omega)
    have he : K+(m+1)-1=K+m := by omega
    rw [he] at h
    exact h
  let EB : FiniteSymmetricChains (PrimeCosetGrid 2 m) (primeGridRank 2 m) m := by
    simpa only [Nat.reduceSub,mul_one] using primeGridSymmetricChains 2 m (by decide)
  let DB := D.pairProduct EB
  letI : Fintype DA.Colour := Fintype.ofFinite _
  letI : Fintype DB.Colour := Fintype.ofFinite _
  have hA : (∑ i : Fin (m+1), ∑ c : D.Colour,
      middlePairWeight K (D.start c) m i.val)=2*A := by
    rw [←D.product_middle_pair_card m,
      DA.rank_card_symm ((K+m)/2) (Nat.div_le_self _ _)]
    change A+A=2*A
    omega
  have hB : (∑ i : Fin (m+1),
      (∑ c : D.Colour,middlePairWeight K (D.start c) m i.val)*m.choose i.val)=2*B := by
    have hw := binaryGrid_weighted_sum m
      (fun i => ∑ c : D.Colour,middlePairWeight K (D.start c) m i)
    have hm : (Finset.univ.filter (fun a : I×PrimeCosetGrid 2 m =>
          rank a.1+primeGridRank 2 m a.2=(K+m)/2)).card +
        (Finset.univ.filter (fun a : I×PrimeCosetGrid 2 m =>
          rank a.1+primeGridRank 2 m a.2=K+m-(K+m)/2)).card =
          ∑ x : PrimeCosetGrid 2 m,∑ c : D.Colour,
            middlePairWeight K (D.start c) m (primeGridRank 2 m x) := by
      rw [D.product_rank_card_right (primeGridRank 2 m) ((K+m)/2),
        D.product_rank_card_right (primeGridRank 2 m) (K+m-(K+m)/2)]
      simp only [middlePairWeight,Finset.sum_add_distrib]
    calc
      (∑ i : Fin (m+1),
          (∑ c : D.Colour,middlePairWeight K (D.start c) m i.val)*m.choose i.val)=
          ∑ i : Fin (m+1),m.choose i.val*
            (∑ c : D.Colour,middlePairWeight K (D.start c) m i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.mul_comm _ _
      _ = ∑ x : PrimeCosetGrid 2 m,∑ c : D.Colour,
            middlePairWeight K (D.start c) m (primeGridRank 2 m x) := hw.symm
      _ = 2*B := by
        rw [←hm,DB.rank_card_symm ((K+m)/2) (Nat.div_le_self _ _)]
        change B+B=2*B
        omega
  have h := middle_pair_binomial_replacement K m D.start D.start_bound
  rw [hA,hB] at h
  have htwo : 2*(2^m*A)≤2*((m+1)*B) := by nlinarith [h]
  exact Nat.le_of_mul_le_mul_left htwo (by decide : 0<2)

end SymmetricSubgroupAsymptotics.FiniteSymmetricChains
