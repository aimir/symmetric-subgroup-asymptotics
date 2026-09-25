import SymmetricSubgroupAsymptotics.CriticalFamilyAsymptotic
import Mathlib.GroupTheory.PGroup

/-!
# Complete fixed-point-free binary families

Here fixed-point-free means no point is fixed by the entire subgroup; it
does not mean that each nonidentity element has no fixed points. The binary
family consists of actual 2-subgroups on the original labelled set. Its
noncritical complement excludes the complete critical orbit-profile family,
including all canonical and noncanonical critical lifts.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- No singleton orbit in the original permutation action. -/
def HasNoFixedPoints {X : Type*} (H : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x : X, ∃ h : H, (h : Equiv.Perm X) x ≠ x

/-- Intrinsic complete binary condition, independent of critical profiles. -/
def IsFixedPointFreeBinary {X : Type*} (H : Subgroup (Equiv.Perm X)) : Prop :=
  IsPGroup 2 H ∧ HasNoFixedPoints H

/-- The full critical action-profile property, with every full lift allowed. -/
def IsEvenCriticalSubgroup (N : ℕ) (H : Subgroup (Equiv.Perm (Fin (2 * N)))) : Prop :=
  ∃ p : criticalProfiles N,
    ∃ e : OrbitProfilePoints criticalActionPoints p.1.multiplicity ≃ Fin (2 * N),
      ∃ K, OrbitProfileFull criticalActionSubgroup 1 K ∧ relabelSubgroup e K = H

/-- All actual fixed-point-free 2-subgroups of S_(2N). -/
abbrev BinarySubgroups (N : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin (2 * N))) // IsFixedPointFreeBinary H}

/-- The complement of all critical profiles within the complete binary family. -/
abbrev NoncriticalBinarySubgroups (N : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin (2 * N))) //
    IsFixedPointFreeBinary H ∧ ¬ IsEvenCriticalSubgroup N H}

theorem criticalAction_moves_point (i : CriticalActionKind) (x : criticalActionPoints i) :
    ∃ u : criticalActionSubgroup i, (u : Equiv.Perm (criticalActionPoints i)) x ≠ x := by
  haveI : Nontrivial (criticalActionPoints i) := by
    cases i <;> dsimp [criticalActionPoints] <;> infer_instance
  obtain ⟨y,hy⟩ := exists_ne x
  obtain ⟨u,hu⟩ := criticalAction_transitive i x y
  exact ⟨u, by rwa [hu]⟩

/-- Actual full block actions move every point when each local action does. -/
theorem OrbitProfileFullOn.hasNoFixedPoints {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {e : OrbitProfilePoints Ω m ≃ X}
    {H : Subgroup (Equiv.Perm X)} (hH : OrbitProfileFullOn U e H)
    (hmove : ∀ i (x : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x ≠ x) :
    HasNoFixedPoints H := by
  intro x
  obtain ⟨⟨i,j,y⟩,rfl⟩ := e.surjective x
  obtain ⟨u,hu⟩ := hmove i y
  obtain ⟨h,hh⟩ := hH.full i j u
  refine ⟨h, ?_⟩
  intro he
  have hxy := e.injective ((hh y).symm.trans he)
  apply hu
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] using hxy

/-- Every full critical model is an actual 2-group, including noncanonical
lifts; faithfulness embeds it in the original exponent-four product. -/
theorem criticalModel_isPGroup (p : CriticalProfile)
    (K : Subgroup (Equiv.Perm (OrbitProfilePoints criticalActionPoints p.multiplicity)))
    (hK : OrbitProfileFull criticalActionSubgroup 1 K) : IsPGroup 2 K := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  obtain ⟨d,hd⟩ := orbitProfileFull_le_product_range hK g.2
  change g.val ^ 4 = 1
  rw [← hd, ← map_pow, criticalOriginalProduct_pow_four, map_one]

/-- The already counted critical family lies in the intrinsically defined
complete binary family. No canonical-kernel restriction is imposed. -/
theorem evenCritical_isFixedPointFreeBinary {N : ℕ}
    {H : Subgroup (Equiv.Perm (Fin (2 * N)))} (hH : IsEvenCriticalSubgroup N H) :
    IsFixedPointFreeBinary H := by
  obtain ⟨p,e,K,hK,rfl⟩ := hH
  constructor
  · exact (criticalModel_isPGroup p.1 K hK).map e.permCongrHom.toMonoidHom
  · have h0 : OrbitProfileFullOn criticalActionSubgroup
        (Equiv.refl (OrbitProfilePoints criticalActionPoints p.1.multiplicity)) K :=
      ⟨hK.maps,hK.full⟩
    have hf := h0.relabel e
    exact hf.hasNoFixedPoints criticalAction_moves_point

/-- Inclusion keeps the literal permutation subgroup unchanged. -/
def evenCriticalToBinary (N : ℕ) : EvenCriticalSubgroups N → BinarySubgroups N :=
  fun H ↦ ⟨H.1, evenCritical_isFixedPointFreeBinary H.2⟩

theorem evenCriticalToBinary_injective (N : ℕ) : Function.Injective (evenCriticalToBinary N) := by
  intro H K h
  exact Subtype.ext (congrArg (fun H : BinarySubgroups N ↦ H.1) h)

/-- Exact disjoint partition of actual subgroups, before taking cardinalities. -/
def binarySubgroupsPartitionEquiv (N : ℕ) :
    BinarySubgroups N ≃ EvenCriticalSubgroups N ⊕ NoncriticalBinarySubgroups N := by
  classical
  refine (Equiv.sumCompl (fun H : BinarySubgroups N ↦ IsEvenCriticalSubgroup N H.1)).symm.trans
    (Equiv.sumCongr ?_ ?_)
  · exact
      { toFun := fun H ↦ ⟨H.1.1,H.2⟩
        invFun := fun H ↦ ⟨evenCriticalToBinary N H,H.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  · exact
      { toFun := fun H ↦ ⟨H.1.1,H.1.2,H.2⟩
        invFun := fun H ↦ ⟨⟨H.1,H.2.1⟩,H.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }

theorem binarySubgroups_card_partition (N : ℕ) :
    Nat.card (BinarySubgroups N) = Nat.card (EvenCriticalSubgroups N) +
      Nat.card (NoncriticalBinarySubgroups N) := by
  letI : Finite (EvenCriticalSubgroups N) :=
    Finite.of_injective _ (evenCriticalToBinary_injective N)
  rw [Nat.card_congr (binarySubgroupsPartitionEquiv N), Nat.card_sum]

theorem binarySubgroups_card_le_subgroupCount (N : ℕ) :
    Nat.card (BinarySubgroups N) ≤ subgroupCount (2 * N) :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem evenCriticalSubgroups_card_le_binary (N : ℕ) :
    Nat.card (EvenCriticalSubgroups N) ≤ Nat.card (BinarySubgroups N) :=
  Nat.card_le_card_of_injective _ (evenCriticalToBinary_injective N)

theorem noncriticalBinarySubgroups_card_le_binary (N : ℕ) :
    Nat.card (NoncriticalBinarySubgroups N) ≤ Nat.card (BinarySubgroups N) := by
  apply Nat.card_le_card_of_injective
    (fun H : NoncriticalBinarySubgroups N ↦ (⟨H.1,H.2.1⟩ : BinarySubgroups N))
  intro H K h
  exact Subtype.ext (congrArg (fun H : BinarySubgroups N ↦ H.1) h)

/-- F_N, normalized by the approved exact coefficient benchmark. -/
def binaryFamilyRatio (N : ℕ) : ℝ :=
  (Nat.card (BinarySubgroups N) : ℝ) / exactBenchmark (2 * N)

/-- E_N excludes all critical actions, not merely canonical lifts. -/
def binaryErrorRatio (N : ℕ) : ℝ :=
  (Nat.card (NoncriticalBinarySubgroups N) : ℝ) / exactBenchmark (2 * N)

def binaryCriticalRatio (N : ℕ) : ℝ :=
  (Nat.card (EvenCriticalSubgroups N) : ℝ) / exactBenchmark (2 * N)

theorem exactBenchmark_even (N : ℕ) :
    exactBenchmark (2 * N) = ((2 * N).factorial : ℝ) *
      (binaryGaussianSum N : ℝ) * (criticalCoefficient N : ℝ) := by
  simp [exactBenchmark, halfDegree, parityCoefficient, parity]

theorem binaryFamilyRatio_partition (N : ℕ) :
    binaryFamilyRatio N = binaryCriticalRatio N + binaryErrorRatio N := by
  unfold binaryFamilyRatio binaryCriticalRatio binaryErrorRatio
  rw [binarySubgroups_card_partition, Nat.cast_add, add_div]

theorem binaryFamilyRatio_nonneg (N : ℕ) : 0 ≤ binaryFamilyRatio N :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos _).le

theorem binaryErrorRatio_nonneg (N : ℕ) : 0 ≤ binaryErrorRatio N :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos _).le

theorem binaryCriticalRatio_nonneg (N : ℕ) : 0 ≤ binaryCriticalRatio N :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos _).le

theorem binaryErrorRatio_le_family (N : ℕ) : binaryErrorRatio N ≤ binaryFamilyRatio N := by
  rw [binaryFamilyRatio_partition]
  exact le_add_of_nonneg_left (binaryCriticalRatio_nonneg N)

theorem binaryCriticalRatio_le_family (N : ℕ) : binaryCriticalRatio N ≤ binaryFamilyRatio N := by
  rw [binaryFamilyRatio_partition]
  exact le_add_of_nonneg_right (binaryErrorRatio_nonneg N)

theorem binaryFamilyRatio_le_ordinary (N : ℕ) :
    binaryFamilyRatio N ≤ (subgroupCount (2 * N) : ℝ) / exactBenchmark (2 * N) := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast binarySubgroups_card_le_subgroupCount N)
    (exactBenchmark_pos _).le

/-- The critical forcing term is bounded independently of the complete
binary count. This imports only the already proved critical-family theorem. -/
theorem binaryCriticalRatio_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, binaryCriticalRatio N ≤ C := by
  obtain ⟨C,hC,hbound⟩ := criticalSubgroups_normalized_bounded
  refine ⟨C,hC,fun N ↦ ?_⟩
  have h := hbound (2 * N)
  rw [criticalSubgroups_even] at h
  exact h

/-- A bounded critical contribution leaves precisely the complete binary
error as the unknown recurrence target. No bound on F_N or E_N is assumed. -/
theorem binaryFamilyRatio_le_error_add_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, binaryFamilyRatio N ≤ C + binaryErrorRatio N := by
  obtain ⟨C,hC,hbound⟩ := binaryCriticalRatio_bounded
  refine ⟨C,hC,fun N ↦ ?_⟩
  rw [binaryFamilyRatio_partition]
  linarith [hbound N]

end SymmetricSubgroupAsymptotics
