import SymmetricSubgroupAsymptotics.FiniteChainGridMiddleBound
import SymmetricSubgroupAsymptotics.SolubleGridSymmetricChains

/-! The exact binomial width estimate for the original soluble coset
shape, transported through actual rank-preserving point equivalences. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

def chainGridAppend : (l h : List ℕ) →
    FiniteChainGrid (l++h) ≃ (FiniteChainGrid l×FiniteChainGrid h)
  | [],h => by
    simpa only [List.nil_append,FiniteChainGrid] using (Equiv.uniqueProd (FiniteChainGrid h) Unit).symm
  | n::l,h => (Equiv.prodCongr (Equiv.refl (Fin n)) (chainGridAppend l h)).trans
      (Equiv.prodAssoc _ _ _).symm

theorem chainGridAppend_rank (l h : List ℕ) (x : FiniteChainGrid (l++h)) :
    FiniteChainGrid.rank l (chainGridAppend l h x).1+
      FiniteChainGrid.rank h (chainGridAppend l h x).2=FiniteChainGrid.rank (l++h) x := by
  induction l with
  | nil =>
    change 0+FiniteChainGrid.rank h x=FiniteChainGrid.rank h x
    exact Nat.zero_add _
  | cons n l ih =>
    rcases x with ⟨i,x⟩
    change (i.val+FiniteChainGrid.rank l (chainGridAppend l h x).1)+
      FiniteChainGrid.rank h (chainGridAppend l h x).2=
        i.val+FiniteChainGrid.rank (l++h) x
    rw [Nat.add_assoc,ih]

def primeGridChains (p : ℕ) : (r : ℕ) →
    PrimeCosetGrid p r ≃ FiniteChainGrid (List.replicate r p)
  | 0 => Equiv.refl Unit
  | r+1 => Equiv.prodCongr (Equiv.refl (Fin p)) (primeGridChains p r)

theorem primeGridChains_rank (p r : ℕ) (x : PrimeCosetGrid p r) :
    FiniteChainGrid.rank (List.replicate r p) (primeGridChains p r x)=primeGridRank p r x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change x.1.val+FiniteChainGrid.rank (List.replicate r p) (primeGridChains p r x.2)=
      x.1.val+primeGridRank p r x.2
    rw [ih]

def SolubleCosetShape.chainLengths : SolubleCosetShape → List ℕ
  | .unit => []
  | .step s p r => s.chainLengths++List.replicate r p

def SolubleCosetShape.chainEquiv : (s : SolubleCosetShape) →
    s.Carrier ≃ FiniteChainGrid s.chainLengths
  | .unit => Equiv.refl Unit
  | .step s p r => (Equiv.prodCongr s.chainEquiv (primeGridChains p r)).trans
      (chainGridAppend s.chainLengths (List.replicate r p)).symm

theorem SolubleCosetShape.chainEquiv_rank (s : SolubleCosetShape) (x : s.Carrier) :
    FiniteChainGrid.rank s.chainLengths (s.chainEquiv x)=s.rank x := by
  induction s with
  | unit => rfl
  | step s p r ih =>
    have h := chainGridAppend_rank s.chainLengths (List.replicate r p) ((SolubleCosetShape.step s p r).chainEquiv x)
    change FiniteChainGrid.rank s.chainLengths
        ((chainGridAppend s.chainLengths (List.replicate r p))
          ((chainGridAppend s.chainLengths (List.replicate r p)).symm
            (s.chainEquiv x.1,primeGridChains p r x.2))).1+
      FiniteChainGrid.rank (List.replicate r p)
        ((chainGridAppend s.chainLengths (List.replicate r p))
          ((chainGridAppend s.chainLengths (List.replicate r p)).symm
            (s.chainEquiv x.1,primeGridChains p r x.2))).2=_ at h
    rw [Equiv.apply_symm_apply] at h
    change FiniteChainGrid.rank (s.chainLengths++List.replicate r p)
      ((SolubleCosetShape.step s p r).chainEquiv x)=s.rank x.1+primeGridRank p r x.2
    rw [←h]
    change FiniteChainGrid.rank s.chainLengths (s.chainEquiv x.1)+
      FiniteChainGrid.rank (List.replicate r p) (primeGridChains p r x.2)=
      s.rank x.1+primeGridRank p r x.2
    rw [ih,primeGridChains_rank]

theorem SolubleCosetShape.chainLengths_maxRank (s : SolubleCosetShape) :
    FiniteChainGrid.maxRank s.chainLengths=s.maxRank := by
  induction s with
  | unit => rfl
  | step s p r ih =>
    simp only [SolubleCosetShape.chainLengths,FiniteChainGrid.maxRank,List.map_append,
      List.sum_append,List.map_replicate,List.sum_replicate,smul_eq_mul]
    change FiniteChainGrid.maxRank s.chainLengths+r*(p-1)=s.maxRank+r*(p-1)
    rw [ih]

theorem SolubleCosetShape.chainLengths_prod (s : SolubleCosetShape) :
    s.chainLengths.prod=s.degree := by
  induction s with
  | unit => rfl
  | step s p r ih =>
    simp only [SolubleCosetShape.chainLengths,List.prod_append,List.prod_replicate,
      SolubleCosetShape.degree,ih]

theorem SolubleCosetShape.chainLengths_positive (s : SolubleCosetShape) (hp : s.Primes) :
    FiniteChainGrid.Positive s.chainLengths := by
  induction s with
  | unit => intro n hn; exact False.elim (List.not_mem_nil hn)
  | step s p r ih =>
    intro n hn
    rcases List.mem_append.mp hn with hn|hn
    · exact ih hp.1 n hn
    · have he := (List.mem_replicate.mp hn).2
      rw [he]
      exact hp.2.pos

/-- Exact finite width bound for the original mixed-prime shape. -/
theorem SolubleCosetShape.middleWidth_binomial (s : SolubleCosetShape) (hp : s.Primes) :
    2^s.maxRank*SolubleCosetShape.middleWidth s≤
      s.degree*s.maxRank.choose (s.maxRank/2) := by
  have h := finiteChainGrid_middle_bound s.chainLengths (s.chainLengths_positive hp) 0
  have hwidth : chainBinaryMiddle s.chainLengths 0=SolubleCosetShape.middleWidth s := by
    let e : s.Carrier ≃ (FiniteChainGrid s.chainLengths×PrimeCosetGrid 2 0) :=
      s.chainEquiv.trans (Equiv.prodUnique (FiniteChainGrid s.chainLengths) Unit).symm
    have he : ∀ x,FiniteChainGrid.rank s.chainLengths (e x).1+
        primeGridRank 2 0 (e x).2=s.rank x := by
      intro x
      exact s.chainEquiv_rank x
    have hr := rank_card_equiv e s.rank
      (fun a => FiniteChainGrid.rank s.chainLengths a.1+primeGridRank 2 0 a.2) he (s.maxRank/2)
    rw [←s.chainLengths_maxRank] at hr
    simpa only [chainBinaryMiddle,SolubleCosetShape.middleWidth,Nat.add_zero,
      s.chainLengths_maxRank] using hr.symm
  rw [hwidth,s.chainLengths_maxRank,s.chainLengths_prod] at h
  simpa only [Nat.add_zero] using h

end SymmetricSubgroupAsymptotics
