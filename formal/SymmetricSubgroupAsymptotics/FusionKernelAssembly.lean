import SymmetricSubgroupAsymptotics.FusionFiniteMenu
import SymmetricSubgroupAsymptotics.FusionCold
import SymmetricSubgroupAsymptotics.FusionHot
import SymmetricSubgroupAsymptotics.FusionZeroWidth
import SymmetricSubgroupAsymptotics.FusionShiftedMenu

/-!
# Physical original-weight fusion installed in the numerical kernels

The local quotient envelope and same-source graph moments imply a bound
on the actual physical subgroup family. Zero-width prefixes have no hot
contribution, by all positive moments. Original action divisors are kept.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

def fusionLocalFactor (b h v : ℕ) (D e : ℝ) : ℝ :=
  D*(2:ℝ)^((((2*h:ℕ):ℝ)-(v:ℝ)-16*e)/8*(b:ℝ))

def fusionLocalThreshold (b v : ℕ) (e : ℝ) : ℝ :=
  (2:ℝ)^(((v:ℝ)/8+e)*(b:ℝ))

def fusionNormalizedPointing (b h : ℕ) (a : ℝ) : ℝ :=
  (((b+2*h).factorial:ℝ)/((b.factorial:ℝ)*a))/exactBenchmark (b+2*h)

theorem fusionLocalThreshold_pos (b v : ℕ) (e : ℝ) :
    0<fusionLocalThreshold b v e := Real.rpow_pos_of_pos (by norm_num) _

theorem fusionLocalThreshold_one_le (b v : ℕ) {e : ℝ} (he : 0≤e) :
    1≤fusionLocalThreshold b v e := by
  exact Real.one_le_rpow (by norm_num) (by positivity)

theorem fusionLocalThreshold_pow (b v q : ℕ) (hq : 1≤q) (e : ℝ) :
    (fusionLocalThreshold b v e)^(q-1) =
      (2:ℝ)^(((q:ℝ)-1)*((v:ℝ)/8+e)*(b:ℝ)) := by
  unfold fusionLocalThreshold
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  rw [Nat.cast_sub hq,Nat.cast_one]
  ring

/-- Exact cold normalization, before any asymptotic estimate. -/
theorem fusionKernel_cold_identity (b h v : ℕ) (D a e s : ℝ) :
    fusionNormalizedPointing b h a * (s*fusionLocalFactor b h v D e*
      fusionLocalThreshold b v e) =
      fusionColdKernel b h D a (16*e) * (s/exactBenchmark b) := by
  have hb := ne_of_gt (exactBenchmark_pos b)
  unfold fusionNormalizedPointing fusionLocalFactor fusionLocalThreshold
    fusionColdKernel fusionPointingRatio
  have he : ((((2*h:ℕ):ℝ)-(v:ℝ)-16*e)/8*(b:ℝ)) +
      (((v:ℝ)/8+e)*(b:ℝ)) = (((h:ℝ)/4-(16*e)/16)*(b:ℝ)) := by
    push_cast
    ring
  rw [← he,Real.rpow_add (by norm_num : (0:ℝ)<2)]
  field_simp

/-- Exact hot normalization at the same-source moment used by the kernel. -/
theorem fusionKernel_hot_identity (s : ℕ → ℝ) (b h v : ℕ) (D a e : ℝ) :
    fusionNormalizedPointing b h a *
      (fusionLocalFactor b h v D e /
        (fusionLocalThreshold b v e)^(fusionMoment e v b-1) *
          s (b+fusionMoment e v b*v)) =
      fusionHotKernel s b h v D a e := by
  rw [fusionLocalThreshold_pow b v _ (fusionMoment_pos e v b)]
  unfold fusionNormalizedPointing fusionLocalFactor fusionHotKernel
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
  ring

theorem fusionNormalizedPointing_nonneg (b h : ℕ) {a : ℝ} (ha : 0<a) :
    0≤fusionNormalizedPointing b h a := by
  have hn := exactBenchmark_pos (b+2*h)
  unfold fusionNormalizedPointing
  positivity

/-- Per-axis actual source sum installed into the original hot/cold kernels.
The all-moment hypothesis handles a zero-width prefix without division by v. -/
theorem fusionKernel_local_sum_le (b h v : ℕ) (f Φ : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    {D a e : ℝ} (hD : 0≤D) (ha : 0<a) (he : 0≤e)
    (hΦ : ∀ J, 0≤Φ J)
    (henvelope : ∀ J, f J≤fusionLocalFactor b h v D e*Φ J)
    (hmoment : ∀ q : ℕ, 1≤q → (∑ J, Φ J^q) ≤ (subgroupCount (b+q*v) : ℝ)) :
    fusionNormalizedPointing b h a * (∑ J, f J) ≤
      fusionMenuHotKernel (fun n => (subgroupCount n : ℝ)) b h v D a e +
        fusionColdKernel b h D a (16*e) * ((subgroupCount b : ℝ)/exactBenchmark b) := by
  have hfactor : 0≤fusionLocalFactor b h v D e := by
    unfold fusionLocalFactor
    positivity
  have hweight := fusionNormalizedPointing_nonneg b h ha
  by_cases hv : v=0
  · have hm : ∀ q : ℕ, 1≤q → (∑ J, Φ J^q) ≤ (subgroupCount b : ℝ) := by
      intro q hq
      simpa only [hv,Nat.mul_zero,Nat.add_zero] using hmoment q hq
    have ht := fusionLocalThreshold_one_le b v he
    have hlocal : (∑ J, f J) ≤
        (subgroupCount b : ℝ)*fusionLocalFactor b h v D e*fusionLocalThreshold b v e := by
      calc
        _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)),
            fusionLocalFactor b h v D e*fusionLocalThreshold b v e := by
          apply Finset.sum_le_sum
          intro J _
          exact (henvelope J).trans (mul_le_mul_of_nonneg_left
            ((fusionZeroWidth_weight_le_one Φ hΦ hm J).trans ht) hfactor)
        _ = _ := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
          unfold subgroupCount
          ring
    calc
      _ ≤ fusionNormalizedPointing b h a *
          ((subgroupCount b : ℝ)*fusionLocalFactor b h v D e*fusionLocalThreshold b v e) :=
        mul_le_mul_of_nonneg_left hlocal hweight
      _ = _ := by rw [fusionKernel_cold_identity]; simp [fusionMenuHotKernel,hv]
  · have hlocal := fusion_hot_cold_sum_le f Φ hfactor (fusionLocalThreshold_pos b v e)
      hΦ henvelope (fusionMoment_pos e v b) (hmoment _ (fusionMoment_pos e v b))
    calc
      _ ≤ fusionNormalizedPointing b h a *
          (fusionLocalFactor b h v D e/(fusionLocalThreshold b v e)^(fusionMoment e v b-1)*
            (subgroupCount (b+fusionMoment e v b*v) : ℝ) +
              (subgroupCount b : ℝ)*fusionLocalFactor b h v D e*fusionLocalThreshold b v e) :=
        mul_le_mul_of_nonneg_left hlocal hweight
      _ = _ := by
        rw [mul_add,fusionKernel_cold_identity]
        rw [fusionKernel_hot_identity (fun n => (subgroupCount n : ℝ))]
        simp only [fusionMenuHotKernel,hv,if_false]

/-- Actual physical original-weight fusion, with both numerical kernels
installed. Every normal is literal; the complete source and original
survival remain inside its local epi count. The only quantitative inputs
are local quotient envelopes and proved same-source graph moments. -/
theorem fusionPhysical_kernel_bound {h : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P)
    (v : {N : Subgroup U // N.Normal} → ℕ)
    (D e : {N : Subgroup U // N.Normal} → ℝ)
    (Φ : {N : Subgroup U // N.Normal} → Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (hD : ∀ N, 0≤D N) (he : ∀ N, 0≤e N) (hΦ : ∀ N J, 0≤Φ N J)
    (henvelope : ∀ N J, fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h (v N) (D N) (e N)*Φ N J)
    (hmoment : ∀ N q, 1≤q → (∑ J, Φ N J^q) ≤
      (subgroupCount (b+q*v N) : ℝ)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        (fusionMenuHotKernel (fun n => (subgroupCount n : ℝ)) b h (v N) (D N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))) : ℝ) (e N) +
        fusionColdKernel b h (D N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))) : ℝ) (16*e N) *
            ((subgroupCount b : ℝ)/exactBenchmark b)) := by
  let a : ℝ := Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h)))))
  have ha : 0<a := by dsimp [a]; exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (U : Set (Equiv.Perm (Fin (2*h))))))
  have hphysical := fusionPhysical_original_weight U P hP
  have hn := div_le_div_of_nonneg_right hphysical (exactBenchmark_pos (b+2*h)).le
  have hnorm :
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b+2*h) ≤ fusionNormalizedPointing b h a *
          ∑ N : {N : Subgroup U // N.Normal},
            ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := by
    convert hn using 1
    simp only [Fintype.card_fin,Nat.cast_sum,Nat.add_comm (2*h) b]
    unfold fusionNormalizedPointing fusionSurvivingEpiCount a
    ring
  calc
    _ ≤ fusionNormalizedPointing b h a *
        ∑ N : {N : Subgroup U // N.Normal},
          ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := hnorm
    _ = ∑ N : {N : Subgroup U // N.Normal},
        fusionNormalizedPointing b h a *
          ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro N _
      exact fusionKernel_local_sum_le b h (v N) (fusionSurvivingEpiCount U P N) (Φ N)
        (hD N) ha (he N) (hΦ N) (henvelope N) (hmoment N)

end SymmetricSubgroupAsymptotics
