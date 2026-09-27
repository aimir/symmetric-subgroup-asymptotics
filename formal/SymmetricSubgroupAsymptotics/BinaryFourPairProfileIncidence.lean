import SymmetricSubgroupAsymptotics.BinaryPairE8Profile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fixed-profile four-pair/E8 incidence with original weights

The reversible local construction is assembled with the actual C2 and E8
normalizers and occurrence factorials.  Four ordered pair occurrences cost
exactly `24 * (e+1)` target-profile units; no tagged E8 colour and no extra
ordering factor is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairProfileIncidence

open PermutationPairOrbitCharacters

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev ExtPoints := BinaryPairE8Profile.exteriorPoints Ω
abbrev ExtMultiplicity := BinaryPairE8Profile.exteriorMultiplicity m
abbrev ExtAction := BinaryPairE8Profile.exteriorAction Ω U

abbrev Model (p e : ℕ) :=
  BinaryDuplicatePairProfile.Model
    (ExtPoints Ω) (ExtMultiplicity m e) (ExtAction Ω U) p

abbrev Physical (p e : ℕ) :=
  BinaryDuplicatePairProfile.Physical
    (ExtPoints Ω) (ExtMultiplicity m e) (ExtAction Ω U) p

def baseDenominator : ℚ := RepeatedMarkerMergedProfile.exteriorDenominator Ω m U
def baseDegree : ℕ := RepeatedMarkerMergedProfile.exteriorDegree Ω m

theorem ext_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ i (x y : ExtPoints Ω i), ∃ u : ExtAction Ω U i,
      (u : Equiv.Perm (ExtPoints Ω i)) x = y := by
  intro i
  cases i with
  | inl _ => exact criticalAction_transitive .e8
  | inr a => exact htrans a

theorem ext_degree_ne_two (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    ∀ i, Fintype.card (ExtPoints Ω i) ≠ 2 := by
  intro i
  cases i with
  | inl _ =>
      change Fintype.card (criticalActionPoints .e8) ≠ 2
      rw [criticalAction_point_card]
      norm_num [criticalActionDegree]
  | inr a => exact hdegree a

theorem exterior_denominator (e : ℕ) :
    RepeatedMarkerMergedProfile.exteriorDenominator
        (ExtPoints Ω) (ExtMultiplicity m e) (ExtAction Ω U) =
      (384 : ℚ)^e * e.factorial * baseDenominator Ω m U := by
  unfold RepeatedMarkerMergedProfile.exteriorDenominator baseDenominator
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, BinaryPairE8Profile.exteriorMultiplicity,
    BinaryPairE8Profile.exteriorAction]
  let c : ℕ := Nat.card (Subgroup.normalizer
    (criticalActionSubgroup .e8 : Set (Equiv.Perm (criticalActionPoints .e8))))
  change (c : ℚ)^e * (e.factorial : ℚ) *
      (∏ a, (Nat.card (Subgroup.normalizer (U a : Set (Equiv.Perm (Ω a)))) : ℚ)^m a *
        (m a).factorial) = _
  have hc : c = 384 := criticalAction_normalizer_card .e8
  rw [hc]
  change 384 ^ e * (e.factorial : ℚ) *
      (∏ a, (Nat.card (Subgroup.normalizer (U a : Set (Equiv.Perm (Ω a)))) : ℚ)^m a *
        (m a).factorial) = _
  unfold RepeatedMarkerMergedProfile.exteriorDenominator
  ring

theorem exterior_degree (e : ℕ) :
    RepeatedMarkerMergedProfile.exteriorDegree (ExtPoints Ω) (ExtMultiplicity m e) =
      8*e + baseDegree Ω m := by
  unfold RepeatedMarkerMergedProfile.exteriorDegree baseDegree
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, BinaryPairE8Profile.exteriorMultiplicity,
    BinaryPairE8Profile.exteriorPoints]
  let d : ℕ := Fintype.card (criticalActionPoints .e8)
  change e * d + (∑ a, m a * Fintype.card (Ω a)) = _
  have hd : d = 8 := by
    simpa [criticalActionDegree] using criticalAction_point_card .e8
  rw [hd]
  change e * 8 + (∑ a, m a * Fintype.card (Ω a)) =
    8 * e + ∑ a, m a * Fintype.card (Ω a)
  omega

theorem model_frame_card_le_target (n e : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    Nat.card (Σ K : Model Ω m U (n+4) e, Frame K.val 4) ≤
      (n+4).descFactorial 4 * Nat.card (Model Ω m U n (e+1)) := by
  calc
    _ ≤ (n+4).descFactorial 4 *
        Nat.card (BinaryPairE8Profile.SourceCover Ω m U n e) :=
      BinaryFourPairFrameModel.model_frame_card_le
        (ExtPoints Ω) (ExtMultiplicity m e) (ExtAction Ω U)
        (ext_transitive Ω U htrans) (ext_degree_ne_two Ω hdegree) n
    _ = (n+4).descFactorial 4 *
        Nat.card (BinaryPairE8Profile.TargetSignFamily Ω m U n (e+1)) := by
      rw [BinaryPairE8Profile.sourceCover_card]
    _ = _ := by
      rw [Nat.card_congr (BinaryDuplicatePairProfile.modelEquiv
        (ExtPoints Ω) (ExtMultiplicity m (e+1)) (ExtAction Ω U) n)]

theorem physical_frame_sum (p e : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated (ExtPoints Ω) (ExtAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : Physical Ω m U p e, (Nat.card (Frame H.val 4) : ℚ)) =
      (((2*p + 8*e + baseDegree Ω m).factorial : ℚ) *
        (∑ K : Model Ω m U p e, (Nat.card (Frame K.val 4) : ℚ))) /
      ((2 : ℚ)^p * p.factorial * (384 : ℚ)^e * e.factorial *
        baseDenominator Ω m U) := by
  have h := assembledOrbitProfile_weighted_sum_rat (fun _ h => h)
    (orbitProfileFull_family_natural
      (RepeatedMarkerMergedProfile.multiplicity (ExtMultiplicity m e) p)
      (RepeatedMarkerMergedProfile.action (ExtPoints Ω) (ExtAction Ω U)))
    (RepeatedMarkerMergedProfile.action_transitive
      (ExtPoints Ω) (ExtAction Ω U) (ext_transitive Ω U htrans))
    (RepeatedMarkerMergedProfile.action_separated
      (ExtPoints Ω) (ExtAction Ω U) hsep (ext_degree_ne_two Ω hdegree))
    (fun K => Nat.card (Frame K 4))
    (fun g K => frame_card_relabel K g 4)
  rw [RepeatedMarkerMergedProfile.degree, RepeatedMarkerMergedProfile.denominator,
    exterior_degree Ω m e, exterior_denominator Ω m U e] at h
  convert h using 1 <;> ring

private theorem profile_weight_identity (n e : ℕ) (A E : ℚ) :
    (((n+4).descFactorial 4 : ℚ) * A) /
        ((2 : ℚ)^(n+4) * (n+4).factorial * 384^e * e.factorial * E) =
      24 * (e+1) * A /
        ((2 : ℚ)^n * n.factorial * 384^(e+1) * (e+1).factorial * E) := by
  by_cases hE : E = 0
  · simp [hE]
  have hfac (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hdesc : (n.factorial : ℚ) * ((n+4).descFactorial 4 : ℚ) =
      ((n+4).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial (n := n+4) (k := 4) (by omega)
  have hefac : (((e+1).factorial : ℕ) : ℚ) = (e+1) * (e.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hpow2 : (2 : ℚ)^(n+4) = 16 * 2^n := by ring_nf
  have hpow384 : (384 : ℚ)^(e+1) = 384^e * 384 := by rw [pow_succ]
  rw [hpow2, hpow384, hefac]
  field_simp [hE, hfac, pow_ne_zero]
  rw [← hdesc]
  ring

/-- The exact fixed-profile Hall incidence.  The source carries actual
ordered independent pair-orbit frames; the target is the ordinary profile
with one additional occurrence of the same E8 colour. -/
theorem normalized_frame_incidence (n e : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated (ExtPoints Ω) (ExtAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : Physical Ω m U (n+4) e, (Nat.card (Frame H.val 4) : ℚ)) /
        (2*(n+4) + 8*e + baseDegree Ω m).factorial ≤
      24 * (e+1) *
        ((Nat.card (Physical Ω m U n (e+1)) : ℚ) /
          (2*n + 8*(e+1) + baseDegree Ω m).factorial) := by
  rw [physical_frame_sum Ω m U (n+4) e htrans hsep hdegree,
    BinaryDuplicatePairProfile.physical_card
      (ExtPoints Ω) (ExtMultiplicity m (e+1)) (ExtAction Ω U) n
      (ext_transitive Ω U htrans) hsep (ext_degree_ne_two Ω hdegree)]
  rw [exterior_degree Ω m (e+1), exterior_denominator Ω m U (e+1)]
  have hfac (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hdegreeEq : 2 * (n + 4) + 8 * e + baseDegree Ω m =
      2 * n + 8 * (e + 1) + baseDegree Ω m := by omega
  rw [hdegreeEq]
  have htargetDegree : 2*n + (8*(e+1) + baseDegree Ω m) =
      2*n + 8*(e+1) + baseDegree Ω m := by omega
  rw [htargetDegree]
  have hcancel (F A D : ℚ) (hF : F ≠ 0) : F * A / D / F = A / D := by
    calc
      _ = (F / F) * (A / D) := by ring
      _ = _ := by rw [div_self hF, one_mul]
  have htargetNorm :
      (((2*n + 8*(e+1) + baseDegree Ω m).factorial : ℚ) *
          (Nat.card (Model Ω m U n (e+1)) : ℚ) /
          ((2 : ℚ)^n * n.factorial *
            ((384 : ℚ)^(e+1) * (e+1).factorial * baseDenominator Ω m U))) /
        ((2*n + 8*(e+1) + baseDegree Ω m).factorial : ℚ) =
      (Nat.card (Model Ω m U n (e+1)) : ℚ) /
        ((2 : ℚ)^n * n.factorial *
          ((384 : ℚ)^(e+1) * (e+1).factorial * baseDenominator Ω m U)) := by
    exact hcancel _ _ _ (hfac _)
  rw [htargetNorm]
  have hsourceNorm :
      (((2*n + 8*(e+1) + baseDegree Ω m).factorial : ℚ) *
          (∑ K : Model Ω m U (n+4) e, (Nat.card (Frame K.val 4) : ℚ)) /
          ((2 : ℚ)^(n+4) * (n+4).factorial * (384 : ℚ)^e * e.factorial *
            baseDenominator Ω m U)) /
        ((2*n + 8*(e+1) + baseDegree Ω m).factorial : ℚ) =
      (∑ K : Model Ω m U (n+4) e, (Nat.card (Frame K.val 4) : ℚ)) /
        ((2 : ℚ)^(n+4) * (n+4).factorial * (384 : ℚ)^e * e.factorial *
          baseDenominator Ω m U) := by
    exact hcancel _ _ _ (hfac _)
  rw [hsourceNorm]
  have hmodelNat := model_frame_card_le_target Ω m U n e htrans hdegree
  have hmodelNat' :
      (∑ K : Model Ω m U (n+4) e, Nat.card (Frame K.val 4)) ≤
        (n+4).descFactorial 4 * Nat.card (Model Ω m U n (e+1)) := by
    simpa only [Nat.card_sigma] using hmodelNat
  have hmodel :
      (∑ K : Model Ω m U (n+4) e, (Nat.card (Frame K.val 4) : ℚ)) ≤
        ((n+4).descFactorial 4 : ℚ) * Nat.card (Model Ω m U n (e+1)) := by
    exact_mod_cast hmodelNat'
  have hbase : 0 < baseDenominator Ω m U := by
    unfold baseDenominator RepeatedMarkerMergedProfile.exteriorDenominator
    apply Finset.prod_pos
    intro a _
    have hcNat : 0 < Nat.card (Subgroup.normalizer
        (U a : Set (Equiv.Perm (Ω a)))) := Nat.card_pos
    have hc : (0 : ℚ) < Nat.card (Subgroup.normalizer
        (U a : Set (Equiv.Perm (Ω a)))) := by exact_mod_cast hcNat
    positivity
  calc
    _ ≤ (((n+4).descFactorial 4 : ℚ) * Nat.card (Model Ω m U n (e+1))) /
        ((2 : ℚ)^(n+4) * (n+4).factorial * 384^e * e.factorial *
          baseDenominator Ω m U) := by
      gcongr
    _ = 24 * (e+1) * (Nat.card (Model Ω m U n (e+1)) : ℚ) /
        ((2 : ℚ)^n * n.factorial * 384^(e+1) * (e+1).factorial *
          baseDenominator Ω m U) := profile_weight_identity n e _ _
    _ = _ := by ring

/-- On `2*N` points the E8 occurrence budget turns the exact profile factor
`24 * (e+1)` into the uniform Hall constant `6*N`. -/
theorem normalized_frame_incidence_six_mul (N n e : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated (ExtPoints Ω) (ExtAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (hsize : 2*n + 8*(e+1) + baseDegree Ω m = 2*N) :
    (∑ H : Physical Ω m U (n+4) e, (Nat.card (Frame H.val 4) : ℚ)) /
        (2*N).factorial ≤
      6*N * ((Nat.card (Physical Ω m U n (e+1)) : ℚ) / (2*N).factorial) := by
  have hsource : 2*(n+4) + 8*e + baseDegree Ω m = 2*N := by omega
  have hdegrees : 2*(n+4) + 8*e + baseDegree Ω m =
      2*n + 8*(e+1) + baseDegree Ω m := by omega
  rw [← hsource, hdegrees]
  have hinc := normalized_frame_incidence Ω m U n e htrans hsep hdegree
  rw [hdegrees] at hinc
  apply hinc.trans
  have he : 24 * (e+1) ≤ 6*N := by omega
  have heq : (24 : ℚ) * (e+1) ≤ 6*N := by exact_mod_cast he
  have hmass : 0 ≤
      (Nat.card (Physical Ω m U n (e+1)) : ℚ) /
        ((2*n + 8*(e+1) + baseDegree Ω m).factorial : ℚ) := by positivity
  exact mul_le_mul_of_nonneg_right heq hmass

end SymmetricSubgroupAsymptotics.BinaryFourPairProfileIncidence
