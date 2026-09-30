import SymmetricSubgroupAsymptotics.Non2PreE7Sns2Menu
import SymmetricSubgroupAsymptotics.BinaryMixtureAbsorption

/-!
# The normalized SNS2 menu mass

The SNS2 rank-tail removes the universal quarter-square cost of its binary
quotient.  This file proves that the remaining literal menu is uniformly
subexponential.  It uses two separately named inputs with their exact roles:

* the Fusari--Spiga subgroup-count consequence for the binary quotient;
* the semisimple outer-factor estimate for a subgroup of `S_w`.

The labelled transitive-action count then aggregates the retained literal
actions.  The desired `PreE7Sns2NormalizedMenuMassBound` is a theorem, not an
assumption.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- **Published input LIT-FUSARI-SPIGA-SUBGROUPS, binary consequence.**
For a finite `2`-group of order `2^l`, the number of normal subgroups, after
removing `2^(l^2/4)`, is at most `8 * 2^(2l)`.  This deliberately weakens the
published explicit subgroup bound and counts normal subgroups by all
subgroups. -/
def FusariSpigaBinaryNormalSubgroupInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G →
    (Nat.card {N : Subgroup G // N.Normal} : ℝ) *
        (2 : ℝ) ^ (-((Nat.log 2 (Nat.card G) : ℝ) ^ 2 / 4)) ≤
      8 * (2 : ℝ) ^ (2 * (Nat.log 2 (Nat.card G) : ℝ))

/-- The uniform outer-factor estimate used by the historical semisimple
argument.  It is stated on the literal semisimple chart inside a permutation
group, before any family or menu aggregation. -/
def SemisimpleOuterFactorPermutationBound : Prop :=
  ∀ (w : ℕ) (U : Subgroup (Equiv.Perm (Fin w)))
      (E : Subgroup U) [E.Normal] (C : SemisimpleNormalChart E) (b : ℕ),
    C.outerFactor (Real.logb 2 (Nat.factorial b)) ≤
      (2 : ℝ) ^
        (3 * (w : ℝ) * (Real.logb 2 ((w + b + 2 : ℕ) : ℝ)) ^ 2)

private theorem eventually_const_le_two_rpow
    {C gamma : ℝ} (hC : 0 ≤ C) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop, C ≤ (2 : ℝ) ^ (gamma * n) := by
  filter_upwards [eventually_exponential_le_inv_rpow hgamma 1,
    eventually_ge_atTop (max 1 ⌈C⌉₊)] with n hexp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hexp' : (2 : ℝ) ^ (-gamma * n) ≤ 1 / (n : ℝ) := by
    simpa using hexp
  have hCn : C ≤ (n : ℝ) :=
    (Nat.le_ceil C).trans
      (by exact_mod_cast (le_max_right 1 ⌈C⌉₊).trans hn)
  have hsmall : C * (2 : ℝ) ^ (-gamma * n) ≤ 1 := by
    calc
      C * (2 : ℝ) ^ (-gamma * n) ≤ C * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp' hC
      _ ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hnpos).2 hCn
  calc
    C = (C * (2 : ℝ) ^ (-gamma * n)) * (2 : ℝ) ^ (gamma * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -gamma * (n : ℝ) + gamma * n = 0 by ring,
        Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (gamma * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

/-- The SNS2 index is a subtype of the original non-pair action classes, so
it inherits the labelled transitive-action bound. -/
theorem preE7Sns2MenuIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7Sns2MenuIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  refine ⟨B, hB, ?_⟩
  intro w
  have hsns2 : Nat.card (PreE7Sns2MenuIndex w) ≤
      Nat.card (PreE7NonPairActionClass w) := Finite.card_subtype_le _
  have hnonpair := preE7NonPairActionClass_card_le_preE7 w
  have hpre := preE7ActionClass_card_le_labelled w
  have hcard : (Nat.card (PreE7Sns2MenuIndex w) : ℝ) ≤
      (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    exact_mod_cast hsns2.trans (hnonpair.trans hpre)
  exact hcard.trans (hcount w)

/-- Pointwise normalized SNS2 coefficient bound retaining the actual quotient
rank and literal semisimple chart. -/
theorem preE7Sns2NormalizedCoefficient_le
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    {w : ℕ} (i : PreE7Sns2MenuIndex w) (b : ℕ) :
    preE7Sns2NormalizedCoefficient i b ≤
      8 * (2 : ℝ) ^
        (2 * (w : ℝ) +
          3 * (w : ℝ) * (Real.logb 2 ((w + b + 2 : ℕ) : ℝ)) ^ 2) := by
  let S := preE7Sns2MenuSource i
  let l := S.quotientRank
  have hFS' := hFS (preE7NonPairAction w i.1 ⧸ S.E) S.quotient_twoGroup
  have hOuter' := hOuter w (preE7NonPairAction w i.1) S.E S.chart b
  have hl : (l : ℝ) ≤ w := by
    have : l ≤ w := by
      have := S.quotient_small
      dsimp [l, PreE7Sns2ActionCertificate.quotientRank]
      omega
    exact_mod_cast this
  have hpow : (2 : ℝ) ^ (2 * (l : ℝ)) ≤
      (2 : ℝ) ^ (2 * (w : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hFS'' :
      (S.quotientNormalCount : ℝ) *
          (2 : ℝ) ^ (-((l : ℝ) ^ 2 / 4)) ≤
        8 * (2 : ℝ) ^ (2 * (w : ℝ)) := by
    exact hFS'.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  unfold preE7Sns2NormalizedCoefficient preE7Sns2MenuCoefficient
  change ((S.quotientNormalCount : ℝ) * S.outerFactor b) *
      (2 : ℝ) ^ (-((l : ℝ) ^ 2 / 4)) ≤ _
  calc
    ((S.quotientNormalCount : ℝ) * S.outerFactor b) *
        (2 : ℝ) ^ (-((l : ℝ) ^ 2 / 4)) =
      ((S.quotientNormalCount : ℝ) *
        (2 : ℝ) ^ (-((l : ℝ) ^ 2 / 4))) * S.outerFactor b := by ring
    _ ≤ (8 * (2 : ℝ) ^ (2 * (w : ℝ))) *
        (2 : ℝ) ^
          (3 * (w : ℝ) *
            (Real.logb 2 ((w + b + 2 : ℕ) : ℝ)) ^ 2) :=
      mul_le_mul hFS'' hOuter' (S.outerFactor_nonneg b)
        (mul_nonneg (by norm_num) (by positivity))
    _ = 8 * ((2 : ℝ) ^ (2 * (w : ℝ)) *
        (2 : ℝ) ^
          (3 * (w : ℝ) *
            (Real.logb 2 ((w + b + 2 : ℕ) : ℝ)) ^ 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- The two structural estimates and the labelled action count prove the
exact normalized menu-mass hypothesis consumed by the SNS2 forward row. -/
theorem preE7Sns2_normalizedMenuMass
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    PreE7Sns2NormalizedMenuMassBound := by
  intro gamma hgamma
  have hquarter : 0 < gamma / 4 := by positivity
  obtain ⟨B, hB, hcount⟩ := preE7Sns2MenuIndex_subquadratic hLMM
    (gamma / 4) hquarter
  let c : ℝ := 1 / Real.log 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let delta : ℝ := Real.sqrt (gamma / 12)
  have hdelta : 0 < delta := Real.sqrt_pos.2 (by positivity)
  filter_upwards [
      BinaryMixtureNumerics.eventually_log_error_le_sqrt c hc hdelta,
      eventually_const_le_two_rpow (C := 8 * B) (gamma := gamma / 4)
        (mul_nonneg (by norm_num) hB) hquarter,
      eventually_ge_atTop (max 1 ⌈8 / gamma⌉₊)] with n hlog hconst hn
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hw5 : 5 ≤ w := hww.1
  have hwn : w ≤ n := by omega
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hwnR : (w : ℝ) ≤ n := by exact_mod_cast hwn
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by exact (le_max_left _ _).trans hn)
  have hgammaN : 8 ≤ gamma * (n : ℝ) := by
    have hceil : 8 / gamma ≤ (n : ℝ) :=
      (Nat.le_ceil (8 / gamma)).trans
        (by exact_mod_cast (le_max_right 1 ⌈8 / gamma⌉₊).trans hn)
    simpa [mul_comm] using (div_le_iff₀ hgamma).mp hceil
  have hlinear : 2 * (w : ℝ) ≤ gamma / 4 * w * n := by
    nlinarith
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hlogb : Real.logb 2 ((n + 2 : ℕ) : ℝ) =
      c * Real.log ((n : ℝ) + 2) := by
    unfold Real.logb c
    norm_num
    ring
  have hlogsq :
      3 * (Real.logb 2 ((n + 2 : ℕ) : ℝ)) ^ 2 ≤
        gamma / 4 * n := by
    rw [hlogb]
    have hsquare := (sq_le_sq₀
      (mul_nonneg hc hlog0) (mul_nonneg hdelta.le hsqrt0)).2 hlog
    have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hdeltaSq : delta ^ 2 = gamma / 12 := by
      dsimp [delta]
      rw [Real.sq_sqrt (by positivity)]
    have hsquare' :
        (c * Real.log ((n : ℝ) + 2)) ^ 2 ≤
          delta ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by
      simpa [mul_pow] using hsquare
    rw [hdeltaSq, hsqrtSq] at hsquare'
    nlinarith
  have houter :
      3 * (w : ℝ) * (Real.logb 2 ((n + 2 : ℕ) : ℝ)) ^ 2 ≤
        gamma / 4 * w * n := by
    nlinarith [mul_le_mul_of_nonneg_left hlogsq hw0]
  have hentry (i : PreE7Sns2MenuIndex w) :
      preE7Sns2NormalizedCoefficient i (n - w) /
          preE7Sns2MenuNormalizer i ≤
        8 * (2 : ℝ) ^ (gamma / 2 * w * n) := by
    have hcoeff := preE7Sns2NormalizedCoefficient_le hFS hOuter i (n - w)
    have hwb : w + (n - w) + 2 = n + 2 := by omega
    rw [hwb] at hcoeff
    have hexponent :
        2 * (w : ℝ) +
            3 * (w : ℝ) * (Real.logb 2 ((n + 2 : ℕ) : ℝ)) ^ 2 ≤
          gamma / 2 * w * n := by
      linarith
    have hnorm : 1 ≤ preE7Sns2MenuNormalizer i := by
      unfold preE7Sns2MenuNormalizer
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7Sns2MenuAction i : Set (Equiv.Perm (Fin w)))))
    exact (div_le_self (preE7Sns2NormalizedCoefficient_nonneg i (n - w))
      hnorm).trans
        (hcoeff.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent)
          (by norm_num)))
  calc
    (∑ i : PreE7Sns2MenuIndex w,
        preE7Sns2NormalizedCoefficient i (n - w) /
          preE7Sns2MenuNormalizer i) ≤
      ∑ _i : PreE7Sns2MenuIndex w,
        8 * (2 : ℝ) ^ (gamma / 2 * w * n) :=
      Finset.sum_le_sum (fun i _ => hentry i)
    _ = (Nat.card (PreE7Sns2MenuIndex w) : ℝ) *
        (8 * (2 : ℝ) ^ (gamma / 2 * w * n)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ (B * (2 : ℝ) ^ (gamma / 4 * (w : ℝ) ^ 2)) *
        (8 * (2 : ℝ) ^ (gamma / 2 * w * n)) :=
      mul_le_mul_of_nonneg_right (hcount w) (by positivity)
    _ = (8 * B) *
        ((2 : ℝ) ^ (gamma / 4 * (w : ℝ) ^ 2) *
          (2 : ℝ) ^ (gamma / 2 * w * n)) := by ring
    _ = (8 * B) *
        (2 : ℝ) ^
          (gamma / 4 * (w : ℝ) ^ 2 + gamma / 2 * w * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (gamma / 4 * n) *
        (2 : ℝ) ^
          (gamma / 4 * (w : ℝ) ^ 2 + gamma / 2 * w * n) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (2 : ℝ) ^
        (gamma / 4 * n + gamma / 4 * (w : ℝ) ^ 2 +
          gamma / 2 * w * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (gamma * w * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
        nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (by positivity : (0 : ℝ) ≤ n),
          mul_nonneg hw0 (sub_nonneg.mpr (sub_nonneg.mpr hwnR))])

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
