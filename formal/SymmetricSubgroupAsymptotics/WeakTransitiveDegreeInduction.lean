import SymmetricSubgroupAsymptotics.WeakTransitivePolylogAbsorption
import SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions
import SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate

/-! A constant-parameter ordinary degree induction and its genuine top
transport. No exact Tracey ceiling or global permutation input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WeakTransitiveDegreeInduction
open WeakTransitivePolylogAbsorption

def rate (n : ℕ) : ℝ := (n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ))

def SmallerRankBound (C : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → ∀ J : Subgroup (Equiv.Perm (Fin k)), 2 ≤ k →
    MulAction.IsPretransitive J (Fin k) → (MarkedC4.genRank J : ℝ) ≤ C * rate k

theorem rank_of_faithful_transitive_action (C : ℝ) (n : ℕ)
    (hbelow : SmallerRankBound C n)
    (H Y : Type) [Group H] [Finite H] [Finite Y] [MulAction H Y] [FaithfulSMul H Y]
    [MulAction.IsPretransitive H Y] (hY : 2 ≤ Nat.card Y) (hlt : Nat.card Y < n) :
    (MarkedC4.genRank H : ℝ) ≤ C * rate (Nat.card Y) := by
  let ePoint := Finite.equivFin Y
  let f : H →* Equiv.Perm (Fin (Nat.card Y)) :=
    ePoint.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H Y)
  have hf : Function.Injective f :=
    ePoint.permCongrHom.injective.comp MulAction.toPerm_injective
  let e : H ≃* f.range := MonoidHom.ofInjective (f := f) hf
  letI : MulAction.IsPretransitive f.range (Fin (Nat.card Y)) := ⟨by
    intro x y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H (ePoint.symm x) (ePoint.symm y)
    refine ⟨⟨f h,h,rfl⟩,?_⟩
    change ePoint (h • ePoint.symm x) = y
    rw [hh,ePoint.apply_symm_apply]⟩
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  exact hbelow (Nat.card Y) hlt f.range hY inferInstance

theorem primitive_step (A : ℕ) (K : ℝ) (hK : 1 ≤ K)
    (n : ℕ) (hn : 2 ≤ n)
    (hscaled : localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤ K * n)
    (g : ℝ) (hg : g ≤ localCharge A n) :
    g ≤ (4 * K) * rate n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) (by linarith only [hnR])
  have hs : 0 < Real.sqrt (Real.logb 2 (n : ℝ)) := Real.sqrt_pos.mpr hL
  have hroot : Real.sqrt (Real.logb 2 (n : ℝ)) ≤ Real.sqrt (Real.logb 2 (n : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith only [hL])
  have hnorm : g * Real.sqrt (Real.logb 2 (n : ℝ)) ≤ (4 * K) * n := by
    calc
      _ ≤ localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hg hs.le
      _ ≤ localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hroot (by dsimp only [localCharge]; positivity)
      _ ≤ K * n := hscaled
      _ ≤ (4 * K) * n := mul_le_mul_of_nonneg_right (by linarith only [hK]) (Nat.cast_nonneg n)
  have hh := (le_div_iff₀ hs).mpr hnorm
  simpa only [rate,mul_div_assoc] using hh

theorem block_step (F K C : ℝ) (hF : 0 ≤ F) (hK : 1 ≤ K) (hC : 4 * K ≤ C)
    (r t : ℕ) (hr : 2 ≤ r) (ht : 2 ≤ t)
    (hscaled : F * Real.sqrt (Real.logb 2 (r : ℝ) + 1) ≤ K * r)
    (g d : ℝ)
    (hsource : g ≤ F * ActualWreathChiefUnitMinimumRate.rate t + d)
    (htop : d ≤ C * rate t) :
    g ≤ C * rate (r * t) := by
  let L := Real.logb 2 (r : ℝ)
  let T := Real.logb 2 (t : ℝ)
  let u := Real.sqrt (L + 1)
  let v := Real.sqrt T
  let w := Real.sqrt (L + T)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 < L := Real.logb_pos (by norm_num) (by linarith only [hrR])
  have hT : 0 < T := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hv : 0 < v := Real.sqrt_pos.mpr hT
  have hw : 0 < w := Real.sqrt_pos.mpr (by linarith only [hL,hT])
  have hC0 : 0 ≤ C := by linarith only [hK,hC]
  have hrate : ActualWreathChiefUnitMinimumRate.rate t ≤ rate t := min_le_right _ _
  have hg : g ≤ (F + C) * (t : ℝ) / v := by
    have hh := hsource.trans (add_le_add (mul_le_mul_of_nonneg_left hrate hF) htop)
    simpa only [rate,←add_mul,mul_div_assoc,T,v] using hh
  have hwu : w / v ≤ u := by
    apply (div_le_iff₀ hv).mpr
    exact ImprimitiveTopLogarithmicScaling.sqrt_log_add_le_mul_sqrt_log L hL.le t ht
  have hnorm : g * w ≤ (F + C) * (t : ℝ) * u := by
    calc
      _ ≤ ((F + C) * (t : ℝ) / v) * w := mul_le_mul_of_nonneg_right hg hw.le
      _ = ((F + C) * (t : ℝ)) * (w / v) := by ring
      _ ≤ ((F + C) * (t : ℝ)) * u :=
        mul_le_mul_of_nonneg_left hwu (mul_nonneg (add_nonneg hF hC0) (Nat.cast_nonneg t))
  have htopScaled : C * u ≤ C * ((3 / 4 : ℝ) * r) :=
    mul_le_mul_of_nonneg_left (sqrt_log_add_one_le_three_quarters r hr) hC0
  have hCr : (4 * K) * (r : ℝ) ≤ C * r :=
    mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg r)
  have hcombined : (F + C) * u ≤ C * r := by
    change F * u ≤ K * r at hscaled
    nlinarith only [hscaled,htopScaled,hCr]
  have hfinal : g * w ≤ C * ((r * t : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hcombined (Nat.cast_nonneg t)
    push_cast
    nlinarith only [hnorm,hh]
  have hlog : Real.logb 2 ((r * t : ℕ) : ℝ) = L + T := by
    rw [Nat.cast_mul,Real.logb_mul (by linarith only [hrR] : (r : ℝ) ≠ 0)
      (by linarith only [htR] : (t : ℝ) ≠ 0)]
  have hh := (le_div_iff₀ hw).mpr hfinal
  simpa only [rate,hlog,mul_div_assoc,w] using hh

end SymmetricSubgroupAsymptotics.WeakTransitiveDegreeInduction
