import SymmetricSubgroupAsymptotics.Non2PreE7RefinedCapacityInstances
import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairMenuMassAggregation

/-!
# Complete numerical menu for the refined-capacity template

The nine refined-capacity families use one exact finite menu of literal
original actions.  The retained carrier/Yoneda source supplies the transfer
parameters and a uniform total envelope before the normalizer divisor is
applied.  `FWRALL` retains its additive tail in the same menu.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

abbrev PreE7RefinedCapacityFamily :=
  {family : PreE7NoPairNoC3EarlierOwnerFamily //
    IsPreE7RefinedCapacityFamily family}

abbrev PreE7RefinedCapacityMenuIndex (w : ℕ) :=
  {p : PreE7RefinedCapacityFamily × PreE7NonPairActionClass w //
    Nonempty (RefinedCapacityCertificateSourceData p.1.1 w p.2)}

noncomputable instance preE7RefinedCapacityMenuIndexFintype (w : ℕ) :
    Fintype (PreE7RefinedCapacityMenuIndex w) :=
  Fintype.ofFinite (PreE7RefinedCapacityMenuIndex w)

noncomputable def preE7RefinedCapacityMenuSource {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) :
    RefinedCapacityCertificateSourceData j.1.1.1 w j.1.2 :=
  Classical.choice j.2

noncomputable def preE7RefinedCapacityMenuCertificate {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) :
    PreE7EarlierActionComparatorCertificate j.1.1.1 w j.1.2 :=
  preE7_refinedCapacityCertificate j.1.1.1 j.1.1.2 w j.1.2
    (preE7RefinedCapacityMenuSource j)

def preE7RefinedCapacityMenuAction {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) :=
  preE7NonPairAction w j.1.2

def preE7RefinedCapacityMenuNormalizer {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7RefinedCapacityMenuAction j : Set (Equiv.Perm (Fin w))))

def preE7RefinedCapacityMainCoefficient {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7RefinedCapacityMenuAction j)
    ((preE7RefinedCapacityMenuCertificate j).C b)

def preE7RefinedCapacityTailCoefficient {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7RefinedCapacityMenuAction j)
    ((preE7RefinedCapacityMenuCertificate j).tailCoefficient b)

theorem preE7RefinedCapacityMenuNormalizer_one_le {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) :
    1 ≤ preE7RefinedCapacityMenuNormalizer j := by
  unfold preE7RefinedCapacityMenuNormalizer
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7RefinedCapacityMenuAction j : Set (Equiv.Perm (Fin w)))))

theorem preE7RefinedCapacityMainCoefficient_nonneg {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) (b : ℕ) :
    0 ≤ preE7RefinedCapacityMainCoefficient j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7RefinedCapacityMenuCertificate j).coefficient_nonneg b)

theorem preE7RefinedCapacityTailCoefficient_nonneg {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) (b : ℕ) :
    0 ≤ preE7RefinedCapacityTailCoefficient j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7RefinedCapacityMenuCertificate j).tail_nonneg b)

private theorem source_main_total_bound
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7RefinedCapacityFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : RefinedCapacityCertificateSourceData family w i) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((preE7_refinedCapacityCertificate family hfamily w i S).C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  all_goals
    simp only [preE7_refinedCapacityCertificate,
      preE7_acertCertificate, preE7_fwrallCertificate,
      preE7_aff128Certificate, preE7_regcapCertificate,
      preE7_ps3capCertificate, preE7_p4capCertificate,
      preE7_acompCertificate, preE7_smallaffCertificate,
      preE7_dzeroCertificate]
  all_goals exact S.coefficient_total_bound b

private theorem source_tail_total_bound
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7RefinedCapacityFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : RefinedCapacityCertificateSourceData family w i) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((preE7_refinedCapacityCertificate family hfamily w i S).tailCoefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  all_goals
    simp only [preE7_refinedCapacityCertificate,
      preE7_acertCertificate, preE7_fwrallCertificate,
      preE7_aff128Certificate, preE7_regcapCertificate,
      preE7_ps3capCertificate, preE7_p4capCertificate,
      preE7_acompCertificate, preE7_smallaffCertificate,
      preE7_dzeroCertificate]
  case fwrall => exact S.tail_total_bound b
  all_goals
    simp [PreE7EarlierActionComparatorCertificate.ofRefinedCapacity,
      fusionAxisEnvelopeTotal]
  all_goals positivity

theorem preE7RefinedCapacityMainCoefficient_bound {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) (b : ℕ) :
    preE7RefinedCapacityMainCoefficient j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) :=
  source_main_total_bound j.1.1.1 j.1.1.2
    (preE7RefinedCapacityMenuSource j) b

theorem preE7RefinedCapacityTailCoefficient_bound {w : ℕ}
    (j : PreE7RefinedCapacityMenuIndex w) (b : ℕ) :
    preE7RefinedCapacityTailCoefficient j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) :=
  source_tail_total_bound j.1.1.1 j.1.1.2
    (preE7RefinedCapacityMenuSource j) b

theorem preE7RefinedCapacityMenuIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7RefinedCapacityMenuIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  let q : ℝ := Nat.card PreE7RefinedCapacityFamily
  refine ⟨q * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have hsub : Nat.card (PreE7RefinedCapacityMenuIndex w) ≤
      Nat.card (PreE7RefinedCapacityFamily ×
        PreE7NonPairActionClass w) := Finite.card_subtype_le _
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  have hprod : (Nat.card (PreE7RefinedCapacityMenuIndex w) : ℝ) ≤
      q * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    calc
      _ ≤ (Nat.card (PreE7RefinedCapacityFamily ×
          PreE7NonPairActionClass w) : ℝ) := by exact_mod_cast hsub
      _ = q * (Nat.card (PreE7NonPairActionClass w) : ℝ) := by
        simp only [Nat.card_prod, Nat.cast_mul, q]
      _ ≤ q * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast haction)
          (Nat.cast_nonneg _)
  exact hprod.trans (by
    calc
      q * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) ≤
          q * (B * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hcount w) (Nat.cast_nonneg _)
      _ = (q * B) * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2) := by ring)

theorem preE7RefinedCapacityMainEnvelope :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7RefinedCapacityMainCoefficient (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7RefinedCapacityMainCoefficient_bound j (n - w))

theorem preE7RefinedCapacityTailEnvelope :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7RefinedCapacityTailCoefficient (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7RefinedCapacityTailCoefficient_bound j (n - w))

theorem preE7RefinedCapacityMainMenuMass
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7RefinedCapacityMainCoefficient (w := w) j b)
      (fun w j => preE7RefinedCapacityMenuNormalizer (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7RefinedCapacityMainCoefficient_nonneg j b)
    (fun _ j => preE7RefinedCapacityMenuNormalizer_one_le j)
    (preE7RefinedCapacityMenuIndex_subquadratic hLMM)
    preE7RefinedCapacityMainEnvelope

theorem preE7RefinedCapacityTailMenuMass
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7RefinedCapacityTailCoefficient (w := w) j b)
      (fun w j => preE7RefinedCapacityMenuNormalizer (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7RefinedCapacityTailCoefficient_nonneg j b)
    (fun _ j => preE7RefinedCapacityMenuNormalizer_one_le j)
    (preE7RefinedCapacityMenuIndex_subquadratic hLMM)
    preE7RefinedCapacityTailEnvelope

private theorem source_parameters
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7RefinedCapacityFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : RefinedCapacityCertificateSourceData family w i) :
    let C := preE7_refinedCapacityCertificate family hfamily w i S
    PreE7CharacterEntryParameters preE7CharacterRho w C.v C.eta C.delta
      C.cutoff C.alpha C.theta := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  all_goals
    simp only [preE7_refinedCapacityCertificate,
      preE7_acertCertificate, preE7_fwrallCertificate,
      preE7_aff128Certificate, preE7_regcapCertificate,
      preE7_ps3capCertificate, preE7_p4capCertificate,
      preE7_acompCertificate, preE7_smallaffCertificate,
      preE7_dzeroCertificate]
  all_goals exact S.parameters

theorem preE7RefinedCapacityParameters :
    GrowingQuotientParameterBound preE7CharacterRho
        (fun w j => (preE7RefinedCapacityMenuCertificate (w := w) j).v)
        (fun w j => (preE7RefinedCapacityMenuCertificate (w := w) j).eta)
        (fun w j => (preE7RefinedCapacityMenuCertificate (w := w) j).delta)
        (fun w j => (preE7RefinedCapacityMenuCertificate (w := w) j).cutoff)
        (fun w j => (preE7RefinedCapacityMenuCertificate (w := w) j).alpha) ∧
      ∀ w j, (preE7RefinedCapacityMenuCertificate (w := w) j).theta ≤
        (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  apply growingQuotientParameterBound_of_entryParameters
  intro w j
  exact source_parameters j.1.1.1 j.1.1.2
    (preE7RefinedCapacityMenuSource j)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
