import SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergy

/-! A bounded exceptional-density sector is cheaper than replacing every
row by its worst rank. Applied to active C3 diagonals, this leaves a strict
quadratic gap below the binary coefficient1/16. No finite group census is
part of this numerical argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergy
variable {I : Type} [Fintype I] [LinearOrder I]

def exceptionalEnergy (P : I → Prop) (c n : I → ℝ) : ℝ :=
  ∑ i : I,∑ j : I,if j<i then (c i-c j)*n j*(if P i then n i else 0) else 0

/-- Equal exceptional densities have no mutual entropy gain. Only the
cross-cut between exceptional and other physical factors can contribute. -/
theorem exceptional_energy_le (P : I → Prop) (c n : I → ℝ) (a : ℝ)
    (ha : 0≤a) (hc0 : ∀ i,0≤c i) (hn : ∀ i,0≤n i)
    (hP : ∀ i,P i → c i=a) :
    exceptionalEnergy P c n≤a*(∑ i : I,n i)^2/4 := by
  let B : ℝ := ∑ i : I,if P i then n i else 0
  let T : ℝ := ∑ i : I,if P i then 0 else n i
  have hp (i j : I) :
      (if j<i then (c i-c j)*n j*(if P i then n i else 0) else 0) ≤
        (if P i then if P j then 0 else a*n i*n j else 0) := by
    by_cases hi : P i
    · by_cases hj : P j
      · simp only [if_pos hi,if_pos hj,hP i hi,hP j hj,sub_self,zero_mul,ite_self,le_refl]
      · by_cases hji : j<i
        · simp only [if_pos hi,if_neg hj,if_pos hji,hP i hi]
          have hh := mul_nonneg (hc0 j) (mul_nonneg (hn i) (hn j))
          nlinarith
        · simp only [if_pos hi,if_neg hj,if_neg hji]
          exact mul_nonneg (mul_nonneg ha (hn i)) (hn j)
    · simp only [if_neg hi,mul_zero,ite_self,le_refl]
  have hsum : exceptionalEnergy P c n≤a*B*T := by
    calc
      _ ≤ ∑ i : I,∑ j : I,if P i then if P j then 0 else a*n i*n j else 0 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
      _ = _ := by
        dsimp [B,T]
        rw [mul_assoc,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hi : P i <;> by_cases hj : P j <;> simp [hi,hj] <;> ring
  have htotal : B+T=∑ i : I,n i := by
    dsimp [B,T]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hcut : B*T≤(∑ i : I,n i)^2/4 := by
    rw [←htotal]
    nlinarith [sq_nonneg (B-T)]
  have hm := mul_le_mul_of_nonneg_left hcut ha
  nlinarith

/-- Ordinary ranks bounded by d*n except for one fixed-density sector
pay d+a*e, rather than the incorrect global maximum d+e. -/
theorem ranked_energy_le_of_exceptional_density
    (P : I → Prop) (c n r : I → ℝ) (d e a : ℝ)
    (hd : 0≤d) (he : 0≤e) (ha : 0≤a)
    (hc0 : ∀ i,0≤c i) (hc1 : ∀ i,c i≤1) (hn : ∀ i,0≤n i)
    (hmono : Monotone c) (hP : ∀ i,P i → c i=a)
    (hr : ∀ i,r i≤d*n i+(if P i then e*n i else 0)) :
    (∑ i : I,∑ j : I,if j<i then (c i-c j)*n j*r i else 0) ≤
      (d+a*e)*(∑ i : I,n i)^2/4 := by
  have hle : (∑ i : I,∑ j : I,if j<i then (c i-c j)*n j*r i else 0) ≤
      d*energy c n+e*exceptionalEnergy P c n := by
    unfold energy exceptionalEnergy
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j<i
    · simp only [if_pos hji]
      have hnon := mul_nonneg (sub_nonneg.mpr (hmono hji.le)) (hn j)
      have hh := mul_le_mul_of_nonneg_left (hr i) hnon
      by_cases hi : P i
      · simp only [if_pos hi] at *
        nlinarith
      · simp only [if_neg hi] at *
        nlinarith
    · simp [hji]
  have hb := mul_le_mul_of_nonneg_left (energy_le_quarter_square c n hc0 hc1 hn) hd
  have hx := mul_le_mul_of_nonneg_left (exceptional_energy_le P c n a ha hc0 hn hP) he
  nlinarith

/-- Ternary specialization: the generic2/9 rank sector plus active C3
rows at density2/3 gives normalized energy at most2/27. -/
theorem ternary_ranked_energy_le (P : I → Prop) (c n r : I → ℝ)
    (hc0 : ∀ i,0≤c i) (hc1 : ∀ i,c i≤1) (hn : ∀ i,0≤n i)
    (hmono : Monotone c) (hP : ∀ i,P i → c i=2/3)
    (hr : ∀ i,r i≤(2/9)*n i+(if P i then (1/9)*n i else 0)) :
    (∑ i : I,∑ j : I,if j<i then (c i-c j)*n j*r i else 0) ≤
      (2/27)*(∑ i : I,n i)^2 := by
  have h := ranked_energy_le_of_exceptional_density P c n r (2/9) (1/9) (2/3)
    (by norm_num) (by norm_num) (by norm_num) hc0 hc1 hn hmono hP hr
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergy
