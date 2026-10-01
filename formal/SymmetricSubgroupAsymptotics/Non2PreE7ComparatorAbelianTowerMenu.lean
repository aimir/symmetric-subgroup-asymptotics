import SymmetricSubgroupAsymptotics.Non2PreE7ComparatorAbelianTowerInstances
import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairMenuMassAggregation
import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage

/-!
# Complete numerical menu for the comparator/abelian-tower template

The sixteen families share one retained-tower incidence theorem and one
linear/log-squared coefficient envelope.  This file selects one literal
source certificate per family/action pair and proves both menu masses and
all hot/cold parameter inequalities uniformly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

abbrev PreE7ComparatorAbelianTowerFamily :=
  {family : PreE7NoPairNoC3EarlierOwnerFamily //
    IsPreE7ComparatorAbelianTowerFamily family}

abbrev PreE7ComparatorAbelianTowerMenuIndex (w : ℕ) :=
  {p : PreE7ComparatorAbelianTowerFamily × PreE7NonPairActionClass w //
    Nonempty (ComparatorAbelianTowerCertificateSourceData p.1.1 w p.2)}

noncomputable instance preE7ComparatorAbelianTowerMenuIndexFintype (w : ℕ) :
    Fintype (PreE7ComparatorAbelianTowerMenuIndex w) :=
  Fintype.ofFinite (PreE7ComparatorAbelianTowerMenuIndex w)

noncomputable def preE7ComparatorAbelianTowerMenuSource {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) :
    ComparatorAbelianTowerCertificateSourceData j.1.1.1 w j.1.2 :=
  Classical.choice j.2

noncomputable def preE7ComparatorAbelianTowerMenuCertificate {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) :
    PreE7EarlierActionComparatorCertificate j.1.1.1 w j.1.2 :=
  preE7_comparatorAbelianTowerCertificate j.1.1.1 j.1.1.2 w j.1.2
    (preE7ComparatorAbelianTowerMenuSource j)

def preE7ComparatorAbelianTowerMenuAction {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) :=
  preE7NonPairAction w j.1.2

def preE7ComparatorAbelianTowerMenuNormalizer {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7ComparatorAbelianTowerMenuAction j :
      Set (Equiv.Perm (Fin w))))

def preE7ComparatorAbelianTowerMainCoefficient {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7ComparatorAbelianTowerMenuAction j)
    ((preE7ComparatorAbelianTowerMenuCertificate j).C b)

def preE7ComparatorAbelianTowerTailCoefficient {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7ComparatorAbelianTowerMenuAction j)
    ((preE7ComparatorAbelianTowerMenuCertificate j).tailCoefficient b)

theorem preE7ComparatorAbelianTowerMenuNormalizer_one_le {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) :
    1 ≤ preE7ComparatorAbelianTowerMenuNormalizer j := by
  unfold preE7ComparatorAbelianTowerMenuNormalizer
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7ComparatorAbelianTowerMenuAction j :
      Set (Equiv.Perm (Fin w)))))

theorem preE7ComparatorAbelianTowerMainCoefficient_nonneg {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) (b : ℕ) :
    0 ≤ preE7ComparatorAbelianTowerMainCoefficient j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7ComparatorAbelianTowerMenuCertificate j).coefficient_nonneg b)

theorem preE7ComparatorAbelianTowerTailCoefficient_nonneg {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) (b : ℕ) :
    0 ≤ preE7ComparatorAbelianTowerTailCoefficient j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7ComparatorAbelianTowerMenuCertificate j).tail_nonneg b)

private theorem source_main_total_bound
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7ComparatorAbelianTowerFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : ComparatorAbelianTowerCertificateSourceData family w i) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((preE7_comparatorAbelianTowerCertificate
          family hfamily w i S).C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  all_goals
    simp only [preE7_comparatorAbelianTowerCertificate,
      preE7_itCertificate, preE7_invCertificate, preE7_pcsCertificate,
      preE7_asCertificate, preE7_cmCertificate, preE7_multCertificate,
      preE7_pcsStarCertificate, preE7_cp3Certificate,
      preE7_towerCertificate, preE7_compCertificate,
      preE7_binirrCertificate, preE7_s3wrCertificate,
      preE7_c3sixCertificate, preE7_s3isoCertificate,
      preE7_s3centCertificate, preE7_cbCertificate]
  all_goals exact S.coefficient_total_bound b

private theorem source_tail_total_bound
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7ComparatorAbelianTowerFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : ComparatorAbelianTowerCertificateSourceData family w i) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((preE7_comparatorAbelianTowerCertificate
          family hfamily w i S).tailCoefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  all_goals
    simp only [preE7_comparatorAbelianTowerCertificate,
      preE7_itCertificate, preE7_invCertificate, preE7_pcsCertificate,
      preE7_asCertificate, preE7_cmCertificate, preE7_multCertificate,
      preE7_pcsStarCertificate, preE7_cp3Certificate,
      preE7_towerCertificate, preE7_compCertificate,
      preE7_binirrCertificate, preE7_s3wrCertificate,
      preE7_c3sixCertificate, preE7_s3isoCertificate,
      preE7_s3centCertificate, preE7_cbCertificate]
  all_goals first
    | exact S.tail_total_bound b
    | simp [PreE7EarlierActionComparatorCertificate.ofAbelianYonedaTowers,
        fusionAxisEnvelopeTotal]
  all_goals positivity

theorem preE7ComparatorAbelianTowerMainCoefficient_bound {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) (b : ℕ) :
    preE7ComparatorAbelianTowerMainCoefficient j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  exact source_main_total_bound j.1.1.1 j.1.1.2
    (preE7ComparatorAbelianTowerMenuSource j) b

theorem preE7ComparatorAbelianTowerTailCoefficient_bound {w : ℕ}
    (j : PreE7ComparatorAbelianTowerMenuIndex w) (b : ℕ) :
    preE7ComparatorAbelianTowerTailCoefficient j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  exact source_tail_total_bound j.1.1.1 j.1.1.2
    (preE7ComparatorAbelianTowerMenuSource j) b

theorem preE7ComparatorAbelianTowerMenuIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7ComparatorAbelianTowerMenuIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  let q : ℝ := Nat.card PreE7ComparatorAbelianTowerFamily
  refine ⟨q * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have hsub : Nat.card (PreE7ComparatorAbelianTowerMenuIndex w) ≤
      Nat.card (PreE7ComparatorAbelianTowerFamily ×
        PreE7NonPairActionClass w) := Finite.card_subtype_le _
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  have hprod : (Nat.card (PreE7ComparatorAbelianTowerMenuIndex w) : ℝ) ≤
      q * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    calc
      _ ≤ (Nat.card (PreE7ComparatorAbelianTowerFamily ×
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

theorem preE7ComparatorAbelianTowerMainEnvelope :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7ComparatorAbelianTowerMainCoefficient
        (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7ComparatorAbelianTowerMainCoefficient_bound j (n - w))

theorem preE7ComparatorAbelianTowerTailEnvelope :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7ComparatorAbelianTowerTailCoefficient
        (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7ComparatorAbelianTowerTailCoefficient_bound j (n - w))

theorem preE7ComparatorAbelianTowerMainMenuMass
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7ComparatorAbelianTowerMainCoefficient
        (w := w) j b)
      (fun w j => preE7ComparatorAbelianTowerMenuNormalizer
        (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7ComparatorAbelianTowerMainCoefficient_nonneg j b)
    (fun _ j => preE7ComparatorAbelianTowerMenuNormalizer_one_le j)
    (preE7ComparatorAbelianTowerMenuIndex_subquadratic hLMM)
    preE7ComparatorAbelianTowerMainEnvelope

theorem preE7ComparatorAbelianTowerTailMenuMass
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7ComparatorAbelianTowerTailCoefficient
        (w := w) j b)
      (fun w j => preE7ComparatorAbelianTowerMenuNormalizer
        (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7ComparatorAbelianTowerTailCoefficient_nonneg j b)
    (fun _ j => preE7ComparatorAbelianTowerMenuNormalizer_one_le j)
    (preE7ComparatorAbelianTowerMenuIndex_subquadratic hLMM)
    preE7ComparatorAbelianTowerTailEnvelope

theorem preE7ComparatorAbelianTowerParameters :
    GrowingQuotientParameterBound preE7CharacterRho
        (fun w j => (preE7ComparatorAbelianTowerMenuCertificate
          (w := w) j).v)
        (fun w j => (preE7ComparatorAbelianTowerMenuCertificate
          (w := w) j).eta)
        (fun w j => (preE7ComparatorAbelianTowerMenuCertificate
          (w := w) j).delta)
        (fun w j => (preE7ComparatorAbelianTowerMenuCertificate
          (w := w) j).cutoff)
        (fun w j => (preE7ComparatorAbelianTowerMenuCertificate
          (w := w) j).alpha) ∧
      ∀ w j, (preE7ComparatorAbelianTowerMenuCertificate (w := w) j).theta ≤
        (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  apply growingQuotientParameterBound_of_entryParameters
  intro w j
  exact preE7_comparatorAbelianTower_entryParameters
    j.1.1.1 j.1.1.2 w j.1.2
      (preE7ComparatorAbelianTowerMenuSource j)

/-- One comparator/tower source supplies the exact numerically complete
package used by the mixed catalogue. -/
noncomputable def preE7ComparatorAbelianTowerNumericalPackage
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7ComparatorAbelianTowerFamily family)
    (w : ℕ) (i : PreE7NonPairActionClass w)
    (source : ComparatorAbelianTowerCertificateSourceData family w i) :
    PreE7EarlierNumericalPackage family w i :=
  .ofComparator
    (preE7_comparatorAbelianTowerCertificate family hfamily w i source)
    (preE7_comparatorAbelianTower_entryParameters
      family hfamily w i source)
    (source_main_total_bound family hfamily source)
    (source_tail_total_bound family hfamily source)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
