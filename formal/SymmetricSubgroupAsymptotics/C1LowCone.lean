import SymmetricSubgroupAsymptotics.C1PhysicalWeight
import SymmetricSubgroupAsymptotics.FusionCold

/-! The actual surviving low one-triple cone has a strict numerical margin.
The rational envelope 3^(3m/20) ≤ 2^(6m/25) follows from 3^5 ≤ 2^8.
It leaves a uniform 1/100 margin against the weaker triple-pointing loss
m/4, and does not use any estimate for the unknown total subgroup count. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

theorem c1_three_le_binary_envelope : (3 : ℝ) ≤ (2 : ℝ)^((8:ℝ)/5) := by
  apply (Real.rpow_le_rpow_iff (by norm_num : (0:ℝ)≤3)
    (by positivity : (0:ℝ)≤(2:ℝ)^((8:ℝ)/5)) (by norm_num : (0:ℝ)<5)).mp
  rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  norm_num [Real.rpow_natCast]

/-- A rational, parity-safe envelope on every actual low-rank source. -/
theorem c1_low_power_le (m d : ℕ) (hd : 20*d≤3*m) :
    (3:ℝ)^d ≤ (2:ℝ)^((6:ℝ)/25*m) := by
  calc
    _ ≤ ((2:ℝ)^((8:ℝ)/5))^d :=
      pow_le_pow_left₀ (by norm_num) c1_three_le_binary_envelope d
    _ = (2:ℝ)^(((8:ℝ)/5)*d) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h : (20:ℝ)*d≤3*m := by exact_mod_cast hd
      linarith

variable {G : Type*} [Group G] [Finite G]

/-- Survival is tested on the original oriented character. No second
source or independent marker maximum is introduced. -/
theorem ternaryLowSurvivingWeight_le (m : ℕ) (S : PrimeCharacters 3 G → Prop) :
    (ternarySurvivingWeight (fun χ => S χ ∧ 20*ternaryCharacterRank G≤3*m):ℝ) ≤
      (2:ℝ)^((6:ℝ)/25*m) := by
  by_cases h : 20*ternaryCharacterRank G≤3*m
  · have hw := ternarySurvivingWeight_le
      (fun χ : PrimeCharacters 3 G => S χ ∧ 20*ternaryCharacterRank G≤3*m)
    have hh : ternarySurvivingWeight
        (fun χ : PrimeCharacters 3 G => S χ ∧ 20*ternaryCharacterRank G≤3*m) ≤
        3^ternaryCharacterRank G := hw.trans (Nat.sub_le _ _)
    exact (show (ternarySurvivingWeight
        (fun χ : PrimeCharacters 3 G => S χ ∧ 20*ternaryCharacterRank G≤3*m):ℝ) ≤
        (3:ℝ)^ternaryCharacterRank G by exact_mod_cast hh).trans
      (c1_low_power_le m _ h)
  · have he : IsEmpty {χ : PrimeCharacters 3 G //
        TernarySplit χ ∧ S χ ∧ 20*ternaryCharacterRank G≤3*m} :=
      ⟨fun χ => h χ.2.2.2⟩
    letI := he
    have hz : ternarySurvivingWeight
        (fun χ : PrimeCharacters 3 G => S χ ∧ 20*ternaryCharacterRank G≤3*m) = 0 := by
      exact Nat.card_eq_zero.mpr (Or.inl he)
    rw [hz,Nat.cast_zero]
    positivity

/-- The cone is defined using the complete literal complement of H. -/
def C1LowGraphPredicate (m : ℕ)
    (P : Subgroup (TernaryCyclic × Equiv.Perm (Fin m)) → Prop)
    (H : Subgroup (TernaryCyclic × Equiv.Perm (Fin m))) : Prop :=
  P H ∧ 20*ternaryCharacterRank
    (H.map (MonoidHom.snd TernaryCyclic (Equiv.Perm (Fin m))))≤3*m

theorem c1LowGraphPredicate_actualGraph (m : ℕ)
    (P : Subgroup (TernaryCyclic × Equiv.Perm (Fin m)) → Prop)
    (K : Subgroup (Equiv.Perm (Fin m))) (χ : PrimeCharacters 3 K) :
    C1LowGraphPredicate m P (ternaryActualGraph ⟨K,χ⟩) ↔
      P (ternaryActualGraph ⟨K,χ⟩) ∧ 20*ternaryCharacterRank K≤3*m := by
  have hr := congrArg (fun L : Subgroup (Equiv.Perm (Fin m)) => ternaryCharacterRank L)
    (ternaryActualGraph_complement ⟨K,χ⟩)
  simp only [C1LowGraphPredicate,hr]

/-- Only after bounding each complete surviving fibre is its number of
sources enlarged to the complete subgroup count s_m. -/
theorem c1Low_surviving_sum_le (m : ℕ)
    (P : Subgroup (TernaryCyclic × Equiv.Perm (Fin m)) → Prop) :
    (∑ K : Subgroup (Equiv.Perm (Fin m)),
      (ternarySurvivingWeight (fun χ : PrimeCharacters 3 K =>
        C1LowGraphPredicate m P (ternaryActualGraph ⟨K,χ⟩)):ℝ)) ≤
      (subgroupCount m:ℝ) * (2:ℝ)^((6:ℝ)/25*m) := by
  have h : ∀ K : Subgroup (Equiv.Perm (Fin m)),
      (ternarySurvivingWeight (fun χ : PrimeCharacters 3 K =>
        C1LowGraphPredicate m P (ternaryActualGraph ⟨K,χ⟩)):ℝ) ≤
          (2:ℝ)^((6:ℝ)/25*m) := by
    intro K
    simpa only [c1LowGraphPredicate_actualGraph] using
      ternaryLowSurvivingWeight_le m
        (fun χ : PrimeCharacters 3 K => P (ternaryActualGraph ⟨K,χ⟩))
  calc
    _ ≤ ∑ _K : Subgroup (Equiv.Perm (Fin m)), (2:ℝ)^((6:ℝ)/25*m) :=
      Finset.sum_le_sum (fun K _ => h K)
    _ = _ := by simp [subgroupCount,Nat.card_eq_fintype_card]

/-- The low cone installed in the actual original-normalizer physical
bound. Naturality is only structural invariance of the actual family. -/
theorem c1Low_physical_card_le (m : ℕ)
    (P : Subgroup (TernaryCyclic × Equiv.Perm (Fin m)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction
      (TernaryPhysicalPredicate (C1LowGraphPredicate m P))) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (TernaryPhysicalPredicate (C1LowGraphPredicate m P))):ℝ) ≤
      ((m+3).factorial:ℝ)/(6*m.factorial) *
        (subgroupCount m:ℝ) * (2:ℝ)^((6:ℝ)/25*m) := by
  have h := ternaryPhysical_original_weight (C1LowGraphPredicate m P) hP
  simp only [Fintype.card_fin,Nat.add_comm 3 m] at h
  exact h.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (c1Low_surviving_sum_le m P)
      (show (0:ℝ)≤((m+3).factorial:ℝ)/(6*m.factorial) by positivity))

end SymmetricSubgroupAsymptotics
