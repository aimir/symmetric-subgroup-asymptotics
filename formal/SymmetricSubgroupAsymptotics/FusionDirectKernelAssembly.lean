import SymmetricSubgroupAsymptotics.FusionKernelAssembly

/-!
# Direct first-moment original-weight fusion

The first same-source moment sends an original width `2*h` to the shifted
degree `b+v`. No hot/cold split or coarse total subgroup estimate is used.
The original action normalizer and literal normal-axis multiplicities remain
in the physical sum. Forwardness is a separate numerical condition `v<2*h`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact coefficient multiplying the normalized subgroup count at `b+v`.
The physical input degree remains `b+2*h`. -/
def fusionDirectKernel (b h v : ℕ) (D a e : ℝ) : ℝ :=
  fusionNormalizedPointing b h a * fusionLocalFactor b h v D e * exactBenchmark (b+v)

theorem fusionDirectKernel_nonneg (b h v : ℕ) {D a e : ℝ}
    (hD : 0≤D) (ha : 0<a) : 0≤fusionDirectKernel b h v D a e := by
  have hp := fusionNormalizedPointing_nonneg b h ha
  have hb := exactBenchmark_pos (b+v)
  unfold fusionDirectKernel fusionLocalFactor
  positivity

/-- Cancellation is exact for both parities of the shifted degree. -/
theorem fusionDirectKernel_identity (b h v : ℕ) (D a e s : ℝ) :
    fusionNormalizedPointing b h a * (fusionLocalFactor b h v D e * s) =
      fusionDirectKernel b h v D a e * (s / exactBenchmark (b+v)) := by
  have hb := ne_of_gt (exactBenchmark_pos (b+v))
  unfold fusionDirectKernel
  field_simp

/-- Only the literal first moment is used. Higher moments and a bound on
the unknown total subgroup sequence are unnecessary for this inequality. -/
theorem fusionDirect_local_sum_le (b h v : ℕ)
    (f Φ : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    {D a e : ℝ} (hD : 0≤D) (ha : 0<a)
    (henvelope : ∀ J, f J≤fusionLocalFactor b h v D e * Φ J)
    (hmoment : (∑ J, Φ J) ≤ (subgroupCount (b+v) : ℝ)) :
    fusionNormalizedPointing b h a * (∑ J, f J) ≤
      fusionDirectKernel b h v D a e *
        ((subgroupCount (b+v) : ℝ)/exactBenchmark (b+v)) := by
  have hf : 0≤fusionLocalFactor b h v D e := by
    unfold fusionLocalFactor
    positivity
  have hsum : (∑ J, f J) ≤ fusionLocalFactor b h v D e *
      (subgroupCount (b+v) : ℝ) := by
    calc
      _ ≤ ∑ J, fusionLocalFactor b h v D e * Φ J :=
        Finset.sum_le_sum (fun J _ => henvelope J)
      _ = fusionLocalFactor b h v D e * ∑ J, Φ J := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmoment hf
  exact (mul_le_mul_of_nonneg_left hsum (fusionNormalizedPointing_nonneg b h ha)).trans_eq
    (fusionDirectKernel_identity b h v D a e _)

/-- Actual physical subgroup count from first moments, before any shifted
row estimate. No normalizer invariance of individual certificates is used. -/
theorem fusionPhysical_direct_bound {h : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P)
    (v : {N : Subgroup U // N.Normal} → ℕ)
    (D e : {N : Subgroup U // N.Normal} → ℝ)
    (Φ : {N : Subgroup U // N.Normal} → Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (hD : ∀ N, 0≤D N)
    (henvelope : ∀ N J, fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h (v N) (D N) (e N)*Φ N J)
    (hmoment : ∀ N, (∑ J, Φ N J) ≤ (subgroupCount (b+v N) : ℝ)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionDirectKernel b h (v N) (D N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))) : ℝ) (e N) *
          ((subgroupCount (b+v N) : ℝ)/exactBenchmark (b+v N)) := by
  let a : ℝ := Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h)))))
  have ha : 0<a := by
    dsimp [a]
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (U : Set (Equiv.Perm (Fin (2*h))))))
  have hphysical := fusionPhysical_original_weight U P hP
  have hn := div_le_div_of_nonneg_right hphysical (exactBenchmark_pos (b+2*h)).le
  have hnorm :
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b+2*h) ≤ fusionNormalizedPointing b h a *
          ∑ N : {N : Subgroup U // N.Normal},
            ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := by
    convert hn using 1
    simp only [Fintype.card_fin, Nat.cast_sum, Nat.add_comm (2*h) b]
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
    _ ≤ _ := Finset.sum_le_sum (fun N _ => fusionDirect_local_sum_le b h (v N)
      (fusionSurvivingEpiCount U P N) (Φ N) (hD N) ha (henvelope N) (hmoment N))

end SymmetricSubgroupAsymptotics

end
