import SymmetricSubgroupAsymptotics.C3TrivialAxisCharacters
import SymmetricSubgroupAsymptotics.C1LowNaturality

/-!
# The full low-rank trivial-axis C3 row

The low-rank estimate does not require the quotient character to split.
Using the exact trivial-axis character classification, all nonzero characters
on each complete source are bounded together.  Thus both the split and
nonsplit-annihilator branches enter the same original-weight contracting row.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The low-rank test is applied to the literal complete complement of the
physical local subgroup. -/
def C3TrivialLowSurvival (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) : Prop :=
  P H ∧ 20*ternaryCharacterRank
    (H.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b)))) ≤ 3*b

def C3TrivialLowPredicate (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) : Prop :=
  FusionAcceptedOrbitPredicate ternaryRegularAction
    (C3TrivialLowSurvival b P) H ∧ H.goursatFst = ⊥

def c3TrivialLowPredicateEquiv (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    {H // C3TrivialLowPredicate b P H} ≃
      C3TrivialAxisLocalFamily (C3TrivialLowSurvival b P) where
  toFun H := ⟨⟨H.1,H.2.1⟩,H.2.2⟩
  invFun H := ⟨H.1.1,H.1.2,H.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem c3PhysicalCharacterGraph_complement (b : ℕ)
    (K : Subgroup (Equiv.Perm (Fin b))) (χ : PrimeCharacters 3 K) :
    (c3PhysicalCharacterGraph K χ).map
      (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b))) = K := by
  exact ternaryPhysicalGraph_complement ⟨K,χ⟩

private theorem c3TrivialLow_character_fibre_le (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (K : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card {χ : {χ : PrimeCharacters 3 K // χ ≠ 0} //
      C3TrivialLowSurvival b P (c3PhysicalCharacterGraph K χ.1)} : ℝ) ≤
        (2:ℝ)^((6:ℝ)/25*b) := by
  let F := {χ : {χ : PrimeCharacters 3 K // χ ≠ 0} //
    C3TrivialLowSurvival b P (c3PhysicalCharacterGraph K χ.1)}
  by_cases hF : Nonempty F
  · let χ : F := Classical.choice hF
    have hrank : 20*ternaryCharacterRank K ≤ 3*b := by
      have h := χ.2.2
      rw [c3PhysicalCharacterGraph_complement] at h
      exact h
    have hcard : Nat.card F ≤ Nat.card (PrimeCharacters 3 K) :=
      Nat.card_le_card_of_injective (fun χ : F => χ.1.1) (by
        intro χ ψ h
        exact Subtype.ext (Subtype.ext h))
    have hchars : Nat.card (PrimeCharacters 3 K) = 3^ternaryCharacterRank K := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3)
        (V := PrimeCharacters 3 K)]
      simp only [Nat.card_zmod,ternaryCharacterRank]
    calc
      (Nat.card F:ℝ) ≤ (Nat.card (PrimeCharacters 3 K):ℝ) := by
        exact_mod_cast hcard
      _ = (3:ℝ)^ternaryCharacterRank K := by rw [hchars]; norm_num
      _ ≤ _ := c1_low_power_le b (ternaryCharacterRank K) hrank
  · letI : IsEmpty F := ⟨fun χ => hF ⟨χ⟩⟩
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance),Nat.cast_zero]
    positivity

/-- The complete local low-rank trivial-axis family has one all-character
factor per complete source. -/
theorem c3TrivialLow_local_card_le (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    (Nat.card {H // C3TrivialLowPredicate b P H}:ℝ) ≤
      (subgroupCount b:ℝ)*(2:ℝ)^((6:ℝ)/25*b) := by
  rw [Nat.card_congr (c3TrivialLowPredicateEquiv b P),
    Nat.card_congr (c3TrivialAxisCharacterEquiv b
      (C3TrivialLowSurvival b P)),Nat.card_sigma,Nat.cast_sum]
  calc
    _ ≤ ∑ K : Subgroup (Equiv.Perm (Fin b)),
        (2:ℝ)^((6:ℝ)/25*b) :=
      Finset.sum_le_sum (fun K _ => c3TrivialLow_character_fibre_le b P K)
    _ = _ := by simp [subgroupCount,Nat.card_eq_fintype_card]

theorem c3TrivialLowSurvival_natural (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    FusionOrbitNatural ternaryRegularAction (C3TrivialLowSurvival b P) := by
  rintro c H ⟨hPs,hrank⟩
  refine ⟨hP c H hPs,?_⟩
  change 20*ternaryCharacterRank
    ((H.map (((ternaryRegularAction.normalizerMonoidHom c.1).prodCongr
      (MulAut.conj c.2)).toMonoidHom)).map
        (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b)))) ≤ 3*b
  rw [fusion_complement_map_prod,ternaryCharacterRank_map_conj]
  exact hrank

theorem c3TrivialLowPredicate_natural (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    FusionOrbitNatural ternaryRegularAction (C3TrivialLowPredicate b P) := by
  rintro c H ⟨⟨hfull,hlow⟩,haxis⟩
  refine ⟨⟨fusion_full_map_prod H hfull
    (ternaryRegularAction.normalizerMonoidHom c.1) (MulAut.conj c.2),
      c3TrivialLowSurvival_natural b P hP c H hlow⟩,?_⟩
  change (H.map (((ternaryRegularAction.normalizerMonoidHom c.1).prodCongr
    (MulAut.conj c.2)).toMonoidHom)).goursatFst = ⊥
  rw [fusion_axis_map_prod,haxis]
  exact Subgroup.map_bot _

theorem c3TrivialLow_physical_card_le (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (C3TrivialLowPredicate b P)):ℝ) ≤
      ((b+3).factorial:ℝ)/(6*b.factorial)*(subgroupCount b:ℝ)*
        (2:ℝ)^((6:ℝ)/25*b) := by
  have h := fusionOrbitFamily_card_le ternaryRegularAction
    (C3TrivialLowPredicate b P) (c3TrivialLowPredicate_natural b P hP)
  rw [ternaryRegularAction_normalizer_card] at h
  simp only [TernaryCyclic,Fintype.card_multiplicative,ZMod.card,Fintype.card_fin,
    Nat.cast_ofNat] at h
  calc
    _ ≤ ((3+b).factorial:ℝ)/(b.factorial*6)*
        Nat.card {H // C3TrivialLowPredicate b P H} := h
    _ ≤ ((3+b).factorial:ℝ)/(b.factorial*6)*
        ((subgroupCount b:ℝ)*(2:ℝ)^((6:ℝ)/25*b)) :=
      mul_le_mul_of_nonneg_left (c3TrivialLow_local_card_le b P) (by positivity)
    _ = _ := by rw [Nat.add_comm 3 b]; ring

def c3TrivialLowKernel (b : ℕ) : ℝ :=
  fusionWidthColdKernel b 3 1 6 ((6:ℝ)/25)

theorem c3TrivialLowKernel_nonneg (b : ℕ) : 0 ≤ c3TrivialLowKernel b :=
  fusionWidthColdKernel_nonneg b 3 (by norm_num) (by norm_num)

theorem c3TrivialLowKernel_eventually :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      c3TrivialLowKernel b ≤ C*(2:ℝ)^(-(1/200:ℝ)*b) := by
  simpa only [c3TrivialLowKernel,halfDegree,
    show (3:ℕ)/2=1 by decide,Nat.cast_one,
    show ((1:ℝ)/4-6/25)/2=1/200 by norm_num] using
    fusionWidthColdKernel_eventually 3 (D := 1) (a := 6) (α := (6:ℝ)/25)
      (by norm_num) (by norm_num) (by norm_num [halfDegree])

theorem c3TrivialLow_physical_normalized (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (C3TrivialLowPredicate b P)):ℝ)/exactBenchmark (b+3) ≤
        c3TrivialLowKernel b*((subgroupCount b:ℝ)/exactBenchmark b) := by
  have hL := exactBenchmark_pos b
  have hN := exactBenchmark_pos (b+3)
  have h := div_le_div_of_nonneg_right (c3TrivialLow_physical_card_le b P hP) hN.le
  apply h.trans_eq
  unfold c3TrivialLowKernel fusionWidthColdKernel fusionWidthPointingRatio
  field_simp

end SymmetricSubgroupAsymptotics

end
