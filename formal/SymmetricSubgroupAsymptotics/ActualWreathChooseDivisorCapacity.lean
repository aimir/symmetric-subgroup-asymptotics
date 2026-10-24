import SymmetricSubgroupAsymptotics.InducedMinimumPrimaryChooseDivisor
import SymmetricSubgroupAsymptotics.ActualWreathChiefDivisorWeights
import SymmetricSubgroupAsymptotics.PrimeGridMiddleElementary

/-! Exact choose-on-divisor capacities on literal local elementary
charts. These strengthen the actual layer, not the older abstract charge
structure whose primePower field requires equality of the whole index.
The floor one is justified by actual prime-grid positivity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChooseDivisorCapacity
open ActualWreathCharacteristicChiefProfile

def primaryRate (q e : ℕ) : ℝ :=
  ((e*(q-1)).choose ((e*(q-1))/2) : ℝ)/(2 : ℝ)^(e*(q-1))

def divisorRate (t q e p : ℕ) : ℝ :=
  if p = q then (t : ℝ)*primaryRate q e else (t : ℝ)/(q : ℝ)^e

def divisorWeight (t q e p : ℕ) : ℝ :=
  max 1 (min ((t : ℝ)/2)
    (min (2*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) (divisorRate t q e p)))

theorem one_le_divisorRate (t q e p : ℕ) (ht : 0 < t) (hq : q.Prime)
    (hd : q^e ∣ t) : 1 ≤ divisorRate t q e p := by
  have hpow : (q : ℝ)^e ≤ t := by exact_mod_cast Nat.le_of_dvd ht hd
  unfold divisorRate
  split_ifs
  · have hmass := primeGrid_binomial_mass_one_le q e hq.pos
    have hrate : 0 ≤ primaryRate q e := by unfold primaryRate; positivity
    calc
      (1 : ℝ) ≤ (q : ℝ)^e*primaryRate q e := by
        simpa only [primaryRate,mul_div_assoc] using hmass
      _ ≤ (t : ℝ)*primaryRate q e := mul_le_mul_of_nonneg_right hpow hrate
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
    exact (le_div_iff₀ (pow_pos hqR e)).mpr
      (by simpa only [one_mul] using hpow)

theorem one_le_divisorWeight (t q e p : ℕ) : 1 ≤ divisorWeight t q e p :=
  le_max_left _ _

theorem divisorWeight_le_divisorRate (t q e p : ℕ) (ht : 0 < t) (hq : q.Prime)
    (hd : q^e ∣ t) : divisorWeight t q e p ≤ divisorRate t q e p :=
  max_le (one_le_divisorRate t q e p ht hq hd)
    ((min_le_right _ _).trans (min_le_right _ _))

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] (phi : S.D →* D')
    (C : ElementaryMinimalNormalChart phi.ker)

theorem layerCapacity_primary_choose (i : I) (e : ℕ)
    (hd : C.p^e ∣ Fintype.card I) :
    (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*Fintype.card I*primaryRate C.p e := by
  have hd' : C.p^e ∣ (S.topPointStabilizer i).index := by
    simpa only [S.topPointStabilizer_index i] using hd
  simpa only [ActualWreathElementaryOrdinaryStep.layerCapacity,
    S.topPointStabilizer_index i,primaryRate,mul_div_assoc] using
    InducedMinimumUniformCapacity.primary_choose_divisor (S.topPointStabilizer i)
      (ActualWreathAffineCapacity.localRepresentation S phi C i) e hd'

theorem layerCapacity_le_divisorWeight (i : I) (hI : 2 ≤ Fintype.card I)
    (q e : ℕ) (hq : q.Prime) (hd : q^e ∣ Fintype.card I) :
    (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*divisorWeight (Fintype.card I) q e C.p := by
  let c := actualCharge S phi C i hI
  have ha : (0 : ℝ) ≤ Module.finrank (ZMod C.p) C.V := by positivity
  have hhalf : (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*((Fintype.card I : ℝ)/2) := by
    simpa only [c,actualCharge,mul_div_assoc] using c.half
  have hlog : (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*
        (2*(Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ))) := by
    have hh := c.logarithmic
    change (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      2*(Module.finrank (ZMod C.p) C.V : ℝ)*(Fintype.card I : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) at hh
    convert hh using 1
    ring
  have hbase : (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*divisorRate (Fintype.card I) q e C.p := by
    by_cases hp : C.p = q
    · have hd' : C.p^e ∣ Fintype.card I := by simpa only [hp] using hd
      have hh := layerCapacity_primary_choose S phi C i e hd'
      simpa only [divisorRate,if_pos hp,hp,mul_assoc] using hh
    · have hh := c.primeTo q e hq (Ne.symm hp) hd
      change (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
        (Module.finrank (ZMod C.p) C.V : ℝ)*(Fintype.card I : ℝ)/(q : ℝ)^e at hh
      simpa only [divisorRate,if_neg hp,mul_div_assoc] using hh
  have hmin : (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*
        min ((Fintype.card I : ℝ)/2)
          (min (2*(Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)))
            (divisorRate (Fintype.card I) q e C.p)) := by
    rw [mul_min_of_nonneg _ _ ha,mul_min_of_nonneg _ _ ha]
    exact le_min hhalf (le_min hlog hbase)
  exact hmin.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)

end SymmetricSubgroupAsymptotics.ActualWreathChooseDivisorCapacity
