import SymmetricSubgroupAsymptotics.FiniteChainGrid

/-! Exact central-binomial width bound for arbitrary finite positive
chain products.  The induction keeps an arbitrary Boolean context. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

def chainBinaryMiddle (l : List ℕ) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : FiniteChainGrid l×PrimeCosetGrid 2 m =>
    FiniteChainGrid.rank l a.1+primeGridRank 2 m a.2=
      (FiniteChainGrid.maxRank l+m)/2)).card

/-- The Boolean context is retained throughout the induction, so replacing
one chain never assumes a general convolution comparison. -/
theorem finiteChainGrid_middle_bound (l : List ℕ) (hl : FiniteChainGrid.Positive l)
    (m : ℕ) :
    2^(FiniteChainGrid.maxRank l)*chainBinaryMiddle l m ≤
      l.prod*(FiniteChainGrid.maxRank l+m).choose ((FiniteChainGrid.maxRank l+m)/2) := by
  induction l generalizing m with
  | nil =>
    have hm : chainBinaryMiddle [] m=m.choose (m/2) := by
      change (Finset.univ.filter (fun a : Unit×PrimeCosetGrid 2 m =>
        0+primeGridRank 2 m a.2=(0+m)/2)).card=m.choose (m/2)
      rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
      simpa only [Fintype.sum_unique,zero_add] using binaryGrid_rank_sum m (m/2)
    simp only [FiniteChainGrid.maxRank,List.map_nil,List.sum_nil,pow_zero,List.prod_nil,
      zero_add,one_mul,hm,le_refl]
  | cons n l ih =>
    have hn : 0<n := hl n (by simp)
    have htail : FiniteChainGrid.Positive l := fun p hp => hl p (by simp [hp])
    let k := n-1
    let K := FiniteChainGrid.maxRank l
    have hkn : k+1=n := by dsimp [k]; omega
    let E : FiniteSymmetricChains (PrimeCosetGrid 2 m) (primeGridRank 2 m) m := by
      simpa only [Nat.reduceSub,mul_one] using primeGridSymmetricChains 2 m (by decide)
    let D := (finiteChainGridSymmetricChains l htail).pairProduct E
    letI : Fintype D.Colour := Fintype.ofFinite _
    let eA : ((FiniteChainGrid l×PrimeCosetGrid 2 m)×Fin (k+1)) ≃
        (FiniteChainGrid (n::l)×PrimeCosetGrid 2 m) := {
      toFun := fun a => ((Fin.cast hkn a.2,a.1.1),a.1.2)
      invFun := fun a => ((a.1.2,a.2),Fin.cast hkn.symm a.1.1)
      left_inv := by intro a; rcases a with ⟨⟨x,y⟩,i⟩; simp
      right_inv := by intro a; rcases a with ⟨⟨i,x⟩,y⟩; simp }
    have hA : (Finset.univ.filter (fun a :
        ((FiniteChainGrid l×PrimeCosetGrid 2 m)×Fin (k+1)) =>
        (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+a.2.val=(K+m+k)/2)).card=
        chainBinaryMiddle (n::l) m := by
      have h := rank_card_equiv eA
        (fun a => (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+a.2.val)
        (fun a => FiniteChainGrid.rank (n::l) a.1+primeGridRank 2 m a.2)
        (by
          intro a
          change a.2.val+FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2=
            (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+a.2.val
          omega) ((K+m+k)/2)
      have he : K+m+k=FiniteChainGrid.maxRank (n::l)+m := by
        change FiniteChainGrid.maxRank l+m+(n-1)=
          (n-1+FiniteChainGrid.maxRank l)+m
        omega
      simpa only [chainBinaryMiddle,he] using h
    let eB : ((FiniteChainGrid l×PrimeCosetGrid 2 m)×PrimeCosetGrid 2 k) ≃
        (FiniteChainGrid l×PrimeCosetGrid 2 (m+k)) :=
      (Equiv.prodAssoc _ _ _).trans
        (Equiv.prodCongr (Equiv.refl _) (binaryGridAppend m k))
    have hB : (Finset.univ.filter (fun a :
        ((FiniteChainGrid l×PrimeCosetGrid 2 m)×PrimeCosetGrid 2 k) =>
        (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+
          primeGridRank 2 k a.2=(K+m+k)/2)).card=chainBinaryMiddle l (m+k) := by
      have h := rank_card_equiv eB
        (fun a => (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+
          primeGridRank 2 k a.2)
        (fun a => FiniteChainGrid.rank l a.1+primeGridRank 2 (m+k) a.2)
        (by
          intro a
          change FiniteChainGrid.rank l a.1.1+
            primeGridRank 2 (m+k) (binaryGridAppend m k (a.1.2,a.2))=_
          rw [binaryGridAppend_rank]
          change FiniteChainGrid.rank l a.1.1+
            (primeGridRank 2 m a.1.2+primeGridRank 2 k a.2)=
            (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+primeGridRank 2 k a.2
          omega) ((K+m+k)/2)
      simpa only [chainBinaryMiddle,K,Nat.add_assoc] using h
    have hreplace : 2^k*chainBinaryMiddle (n::l) m≤n*chainBinaryMiddle l (m+k) := by
      have h := D.middle_card_chain_le_binary k
      change 2^k*(Finset.univ.filter (fun a :
          ((FiniteChainGrid l×PrimeCosetGrid 2 m)×Fin (k+1)) =>
          (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+a.2.val=(K+m+k)/2)).card≤
        (k+1)*(Finset.univ.filter (fun a :
          ((FiniteChainGrid l×PrimeCosetGrid 2 m)×PrimeCosetGrid 2 k) =>
          (FiniteChainGrid.rank l a.1.1+primeGridRank 2 m a.1.2)+
            primeGridRank 2 k a.2=(K+m+k)/2)).card at h
      rw [hA,hB,hkn] at h
      exact h
    have hIH := ih htail (m+k)
    have hmax : FiniteChainGrid.maxRank (n::l)=K+k := by
      change (n-1)+FiniteChainGrid.maxRank l=FiniteChainGrid.maxRank l+(n-1)
      exact Nat.add_comm _ _
    have he : (FiniteChainGrid.maxRank l+(m+k)).choose
        ((FiniteChainGrid.maxRank l+(m+k))/2)=
        (FiniteChainGrid.maxRank (n::l)+m).choose
          ((FiniteChainGrid.maxRank (n::l)+m)/2) := by
      rw [hmax]
      congr 1 <;> dsimp [K] <;> omega
    calc
      2^(FiniteChainGrid.maxRank (n::l))*chainBinaryMiddle (n::l) m=
          2^K*(2^k*chainBinaryMiddle (n::l) m) := by rw [hmax,pow_add]; ring
      _ ≤ 2^K*(n*chainBinaryMiddle l (m+k)) := Nat.mul_le_mul_left _ hreplace
      _ = n*(2^K*chainBinaryMiddle l (m+k)) := by ring
      _ ≤ n*(l.prod*(FiniteChainGrid.maxRank l+(m+k)).choose
          ((FiniteChainGrid.maxRank l+(m+k))/2)) := Nat.mul_le_mul_left _ hIH
      _ = (n::l).prod*(FiniteChainGrid.maxRank (n::l)+m).choose
          ((FiniteChainGrid.maxRank (n::l)+m)/2) := by rw [he,List.prod_cons]; ring

end SymmetricSubgroupAsymptotics
