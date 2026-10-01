import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage
import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogueAssembly
import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared
import SymmetricSubgroupAsymptotics.Non2PreE7EmptyCellNumerics

/-!
# Numerically complete mixed pre-E7 catalogue

This is the all-width integration of the family templates.  An earlier cell
is present only when its literal action carries a numerically complete
package.  Empty owner/action pairs receive the proved harmless parameters.
The terminal row is supplied in the same numerical shape.  From those local
facts the global parameter record and both menu masses are theorems.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

theorem preE7NoPairNoC3NumericalCertifiedFirstOwnerPredicate_implies_broad
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w)
    (b : ℕ)
    (H : Subgroup
      (preE7NonPairFirstOwnerAction w j × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierNumericalFamilyAction w j b H →
      preE7NoPairNoC3BroadActionPredicate w j.2 b H := by
  rintro ⟨⟨⟨hordinary, _howner⟩, hnoC3⟩, _hselected⟩
  exact ⟨hordinary, hnoC3⟩

/-- One exact row of the numerical catalogue. -/
structure PreE7NoPairNoC3NumericalExceptionalChoice
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w) where
  D : ℕ → ℝ
  T : ℕ → ℝ
  X : ℕ → ℝ
  v : ℕ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  main_total_bound : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_total_bound : ∀ b,
    T b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  exceptional : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
    ExponentialScalarBound X
  exceptional_support : X = 0 ∨ w ≤ 12288
  local_bound : ∀ b,
    (Nat.card (FusionOrbitFamily
        (preE7NonPairFirstOwnerAction w j)
        (FusionAcceptedOrbitPredicate
          (preE7NonPairFirstOwnerAction w j)
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierNumericalFamilyAction w j b))) : ℝ) /
        exactBenchmark (b + w) ≤
      (growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w j :
              Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta cutoff +
        fusionWidthColdKernel b w (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w j :
              Set (Equiv.Perm (Fin w)))) : ℝ)
          alpha * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w (T b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w j :
              Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ordinarySubgroupRatio b) + X b

namespace PreE7NoPairNoC3NumericalExceptionalChoice

/-- Install one matching numerical earlier-owner package. -/
noncomputable def ofEarlierPackage
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (C : PreE7EarlierNumericalPackage
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    PreE7NoPairNoC3NumericalExceptionalChoice w (k.castSucc, U) where
  D := C.package.certificate.D
  T := C.package.certificate.T
  X := C.package.certificate.X
  v := C.package.certificate.v
  eta := C.package.certificate.eta
  delta := C.package.certificate.delta
  cutoff := C.package.certificate.cutoff
  alpha := C.package.certificate.alpha
  theta := C.package.certificate.theta
  alpha_eq := C.package.certificate.alpha_eq
  D_nonneg := C.package.certificate.D_nonneg
  T_nonneg := C.package.certificate.T_nonneg
  parameters := C.parameters
  main_total_bound := C.main_total_bound
  tail_total_bound := C.tail_total_bound
  exceptional := C.package.exceptional
  exceptional_support := C.package.exceptional_support
  local_bound := fun b => C.package.certificate.local_bound b _
    (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
      (k.castSucc, U) b)
    (preE7NoPairNoC3NumericalCertifiedFirstOwnerPredicate_implies_broad
      w (k.castSucc, U) b)

/-- A nonmatching numerical owner/action cell is empty and carries the proved
empty-cell transfer parameters. -/
noncomputable def emptyEarlier
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hmissing : ¬ preE7NoPairNoC3EarlierNumericalFamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    PreE7NoPairNoC3NumericalExceptionalChoice w (k.castSucc, U) where
  D := fun _ => 0
  T := fun _ => 0
  X := fun _ => 0
  v := preE7EmptyCellDegree w
  eta := 0
  delta := preE7EmptyCellDelta w
  cutoff := preE7EmptyCellCutoff w
  alpha := preE7EmptyCellAlpha w
  theta := 0
  alpha_eq := by simp [preE7EmptyCellAlpha]
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun _ => le_rfl
  parameters := preE7EmptyCell_entryParameters
    (preE7NonPairAction_width_three_le U)
  main_total_bound := fun _ => by positivity
  tail_total_bound := fun _ => by positivity
  exceptional := fun _ =>
    { threshold := 0
      rate := 1
      constant := 1
      rate_pos := by norm_num
      constant_pos := by norm_num
      bound := by simp }
  exceptional_support := Or.inl rfl
  local_bound := by
    intro b
    let U' := preE7NonPairFirstOwnerAction w (k.castSucc, U)
    let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
      preE7NoPairNoC3EarlierNumericalFamilyAction w (k.castSucc, U) b
    haveI : IsEmpty (FusionOrbitFamily U'
        (FusionAcceptedOrbitPredicate U' P)) := by
      refine ⟨fun K => ?_⟩
      obtain ⟨_, ⟨⟨s, ⟨M, hM⟩⟩, rfl⟩⟩ := K
      obtain ⟨⟨H, hH⟩, rfl⟩ := hM
      exact hmissing
        ((preE7NoPairNoC3SelectedActionEligible_castSucc
          preE7NoPairNoC3EarlierNumericalFamilyAction k U).mp hH.2.2)
    have hcard : Nat.card (FusionOrbitFamily U'
        (FusionAcceptedOrbitPredicate U' P)) = 0 := Nat.card_of_isEmpty
    change (Nat.card (FusionOrbitFamily U'
        (FusionAcceptedOrbitPredicate U' P)) : ℝ) /
          exactBenchmark (b + w) ≤ _
    rw [hcard]
    simp [growingQuotientHotKernel, fusionWidthColdKernel]

end PreE7NoPairNoC3NumericalExceptionalChoice

/-- Select the numerical earlier package, an empty cell, or the supplied
terminal row. -/
noncomputable def preE7NoPairNoC3NumericalExceptionalChoice
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3NumericalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
    (w : ℕ)
    (owner : Fin (preE7NoPairNoC3EarlierOwnerCount + 1))
    (U : PreE7NonPairActionClass w) :
    PreE7NoPairNoC3NumericalExceptionalChoice w (owner, U) := by
  classical
  by_cases ho : owner.val < preE7NoPairNoC3EarlierOwnerCount
  · let k : Fin preE7NoPairNoC3EarlierOwnerCount := ⟨owner.val, ho⟩
    have howner : owner = k.castSucc := by apply Fin.ext; rfl
    by_cases hC : preE7NoPairNoC3EarlierNumericalFamilyAction
        (preE7NoPairNoC3EarlierOwnerEquiv k) w U
    · simpa only [howner] using
        (PreE7NoPairNoC3NumericalExceptionalChoice.ofEarlierPackage
          k U (Classical.choice hC))
    · simpa only [howner] using
        (PreE7NoPairNoC3NumericalExceptionalChoice.emptyEarlier k U hC)
  · have howner : owner = Fin.last preE7NoPairNoC3EarlierOwnerCount :=
      Fin.eq_last_of_not_lt ho
    simpa only [howner] using Residual w U

/-- Assemble the numerical earlier catalogue and terminal rows into the
physical exceptional interface. -/
noncomputable def preE7NoPairNoC3_numericalExceptionalData
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3NumericalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U)) :
    PreE7NoPairNoC3LocalExceptionalData
      preE7NoPairNoC3EarlierOwnerCount where
  P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
    preE7NoPairNoC3EarlierNumericalFamilyAction
  P_natural := preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _
  physical_cover :=
    preE7NoPairNoC3_certifiedOwnerOrResidual_physical_cover _
  D := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).D
  T := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).T
  X := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).X
  A := fun w j => Nat.card (Subgroup.normalizer
    (preE7NonPairFirstOwnerAction w j : Set (Equiv.Perm (Fin w))))
  v := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).v
  eta := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).eta
  delta := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).delta
  cutoff := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).cutoff
  alpha := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).alpha
  theta := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).theta
  D_nonneg := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).D_nonneg
  T_nonneg := fun w j =>
    (preE7NoPairNoC3NumericalExceptionalChoice Residual w j.1 j.2).T_nonneg
  A_eq := fun _ _ => rfl
  local_bound := by
    intro n j
    let w : ℕ := j.1.1
    let C := preE7NoPairNoC3NumericalExceptionalChoice
      Residual w j.2.1 j.2.2
    have hwn : w ≤ n := growingQuotientPhysicalWidth_le j
    have h := C.local_bound (n - w)
    rw [GrowingQuotientCanonicalFamily, fusionWidthCanonicalFamily_card]
    simpa only [w, C, Nat.sub_add_cancel hwn] using h

private theorem numericalIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount
      (fun w => PreE7NonPairFirstOwnerIndex
        (preE7NoPairNoC3EarlierOwnerCount + 1) w) := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  let q : ℕ := preE7NoPairNoC3EarlierOwnerCount + 1
  refine ⟨(q : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  calc
    (Nat.card (PreE7NonPairFirstOwnerIndex
        (preE7NoPairNoC3EarlierOwnerCount + 1) w) : ℝ) =
        (q : ℝ) * (Nat.card (PreE7NonPairActionClass w) : ℝ) := by
      simp only [PreE7NonPairFirstOwnerIndex, Nat.card_prod, Nat.card_fin,
        Nat.cast_mul, q]
    _ ≤ (q : ℝ) * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast haction)
        (Nat.cast_nonneg _)
    _ ≤ (q : ℝ) * (B * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcount w) (Nat.cast_nonneg _)
    _ = ((q : ℝ) * B) * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2) := by ring

private theorem numericalMain_envelope
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3NumericalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U)) :
    LinearLogSquaredMenuNumeratorBound 3
      (preE7NoPairNoC3_numericalExceptionalData Residual).D := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [preE7NoPairNoC3_numericalExceptionalData, zero_mul,
    zero_add, one_mul, hwb, Nat.cast_add, Nat.cast_ofNat] using
    (preE7NoPairNoC3NumericalExceptionalChoice
      Residual w j.1 j.2).main_total_bound (n - w)

private theorem numericalTail_envelope
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3NumericalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U)) :
    LinearLogSquaredMenuNumeratorBound 3
      (preE7NoPairNoC3_numericalExceptionalData Residual).T := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [preE7NoPairNoC3_numericalExceptionalData, zero_mul,
    zero_add, one_mul, hwb, Nat.cast_add, Nat.cast_ofNat] using
    (preE7NoPairNoC3NumericalExceptionalChoice
      Residual w j.1 j.2).tail_total_bound (n - w)

/-- The complete global numerical certificate follows from the retained
entry numerics and the labelled transitive-action count. -/
noncomputable def preE7NoPairNoC3_numericalExceptionalCertificate
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3NumericalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    PreE7NoPairNoC3LocalExceptionalNumericalCertificate
      (preE7NoPairNoC3_numericalExceptionalData Residual) where
  rho := preE7CharacterRho
  rho_pos := by norm_num [preE7CharacterRho]
  rho_le_eighth := by norm_num [preE7CharacterRho]
  parameters := (growingQuotientParameterBound_of_entryParameters
    (fun (w : ℕ) (j : PreE7NonPairFirstOwnerIndex
        (preE7NoPairNoC3EarlierOwnerCount + 1) w) =>
      (preE7NoPairNoC3NumericalExceptionalChoice
      Residual w j.1 j.2).parameters)).1
  tail_gap := (growingQuotientParameterBound_of_entryParameters
    (fun (w : ℕ) (j : PreE7NonPairFirstOwnerIndex
        (preE7NoPairNoC3EarlierOwnerCount + 1) w) =>
      (preE7NoPairNoC3NumericalExceptionalChoice
      Residual w j.1 j.2).parameters)).2
  main_menu := growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (preE7NoPairNoC3_numericalExceptionalData Residual).D_nonneg
    (fun w j => by
      change (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w j : Set (Equiv.Perm (Fin w))))
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w j : Set (Equiv.Perm (Fin w))))))
    (numericalIndex_subquadratic hLMM)
    (numericalMain_envelope Residual)
  tail_menu := growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (preE7NoPairNoC3_numericalExceptionalData Residual).T_nonneg
    (fun w j => by
      change (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w j : Set (Equiv.Perm (Fin w))))
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w j : Set (Equiv.Perm (Fin w))))))
    (numericalIndex_subquadratic hLMM)
    (numericalTail_envelope Residual)
  exceptional := by
    apply exponentialScalarBound_growingQuotientExceptionalTotal 3 12288
    · intro w j
      exact (preE7NoPairNoC3NumericalExceptionalChoice
        Residual w j.1 j.2).exceptional hcoarse
    · intro w j hw
      change (preE7NoPairNoC3NumericalExceptionalChoice
        Residual w j.1 j.2).X = 0
      rcases (preE7NoPairNoC3NumericalExceptionalChoice
        Residual w j.1 j.2).exceptional_support with hzero | hwidth
      · exact hzero
      · omega

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
