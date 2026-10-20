import SymmetricSubgroupAsymptotics.SolubleGridMiddleBound

/-! Exact normalized middle width of the original prime coset grid. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

def primeGridMiddleWidth (p t : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : PrimeCosetGrid p t =>
    primeGridRank p t x=(t*(p-1))/2)).card

theorem primeGridMiddleWidth_binomial (p t : ℕ) (hp : 0<p) :
    2^(t*(p-1))*primeGridMiddleWidth p t≤
      p^t*(t*(p-1)).choose ((t*(p-1))/2) := by
  have hpos : FiniteChainGrid.Positive (List.replicate t p) := by
    intro q hq
    rw [(List.mem_replicate.mp hq).2]
    exact hp
  have h := finiteChainGrid_middle_bound (List.replicate t p) hpos 0
  have hK : FiniteChainGrid.maxRank (List.replicate t p)=t*(p-1) := by
    simp only [FiniteChainGrid.maxRank,List.map_replicate,List.sum_replicate,smul_eq_mul]
  let e : PrimeCosetGrid p t ≃
      (FiniteChainGrid (List.replicate t p)×PrimeCosetGrid 2 0) :=
    (primeGridChains p t).trans
      (Equiv.prodUnique (FiniteChainGrid (List.replicate t p)) Unit).symm
  have he : ∀ x,FiniteChainGrid.rank (List.replicate t p) (e x).1+
      primeGridRank 2 0 (e x).2=primeGridRank p t x := by
    intro x
    exact primeGridChains_rank p t x
  have hc := rank_card_equiv e (primeGridRank p t)
    (fun a => FiniteChainGrid.rank (List.replicate t p) a.1+primeGridRank 2 0 a.2)
    he ((t*(p-1))/2)
  have hw : chainBinaryMiddle (List.replicate t p) 0=primeGridMiddleWidth p t := by
    simpa only [chainBinaryMiddle,primeGridMiddleWidth,hK,Nat.add_zero] using hc.symm
  rw [hw,hK,List.prod_replicate] at h
  simpa only [Nat.add_zero] using h

theorem primeGrid_antichain_card_le_middle (p t : ℕ) (hp : 0<p)
    (s : Finset (PrimeCosetGrid p t))
    (hs : IsAntichain (· ≤ ·) (s : Set (PrimeCosetGrid p t))) :
    s.card≤primeGridMiddleWidth p t :=
  (primeGridSymmetricChains p t hp).antichain_card_le_middle s hs

end SymmetricSubgroupAsymptotics
