import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateInstances
import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairMenuMassAggregation

/-!
# Complete numerical menu for the character-certificate template

The character source already proves every local quotient estimate.  The
numerical menu source additionally retains the two total literal-axis
envelopes needed to sum over original actions.  This is the precise global
datum that cannot be recovered from separate worst-case axis bounds.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A character source with the two global literal-axis totals retained.
The totals use the template coefficients, which are independent of the proof
of the literature inputs used in the local epimorphism theorem. -/
structure PreE7CharacterMenuSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7CharacterFamily family)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  source : CharacterCertificateSourceData family w i
  main_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((CharacterCertificateSourceData.toTemplateData
          family hfamily source).mainCoefficient) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((CharacterCertificateSourceData.toTemplateData
          family hfamily source).tailCoefficient) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

abbrev PreE7CharacterFamily :=
  {family : PreE7NoPairNoC3EarlierOwnerFamily //
    IsPreE7CharacterFamily family}

abbrev PreE7CharacterMenuIndex (w : ℕ) :=
  {p : PreE7CharacterFamily × PreE7NonPairActionClass w //
    Nonempty (PreE7CharacterMenuSourceData p.1.1 p.1.2 w p.2)}

noncomputable instance preE7CharacterMenuIndexFintype (w : ℕ) :
    Fintype (PreE7CharacterMenuIndex w) :=
  Fintype.ofFinite (PreE7CharacterMenuIndex w)

noncomputable def preE7CharacterMenuSource {w : ℕ}
    (j : PreE7CharacterMenuIndex w) :
    PreE7CharacterMenuSourceData j.1.1.1 j.1.1.2 w j.1.2 :=
  Classical.choice j.2

noncomputable def preE7CharacterMenuCertificate
    (lit : PreE7CharacterLiterature) {w : ℕ}
    (j : PreE7CharacterMenuIndex w) :
    PreE7EarlierActionComparatorCertificate j.1.1.1 w j.1.2 :=
  preE7_characterCertificate j.1.1.1 j.1.1.2 w j.1.2
    (preE7CharacterMenuSource j).source lit

def preE7CharacterMenuAction {w : ℕ} (j : PreE7CharacterMenuIndex w) :=
  preE7NonPairAction w j.1.2

def preE7CharacterMenuNormalizer {w : ℕ}
    (j : PreE7CharacterMenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7CharacterMenuAction j : Set (Equiv.Perm (Fin w))))

def preE7CharacterMainCoefficient (lit : PreE7CharacterLiterature)
    {w : ℕ} (j : PreE7CharacterMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7CharacterMenuAction j)
    ((preE7CharacterMenuCertificate lit j).C b)

def preE7CharacterTailCoefficient (lit : PreE7CharacterLiterature)
    {w : ℕ} (j : PreE7CharacterMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7CharacterMenuAction j)
    ((preE7CharacterMenuCertificate lit j).tailCoefficient b)

theorem preE7CharacterMenuNormalizer_one_le {w : ℕ}
    (j : PreE7CharacterMenuIndex w) :
    1 ≤ preE7CharacterMenuNormalizer j := by
  unfold preE7CharacterMenuNormalizer
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7CharacterMenuAction j : Set (Equiv.Perm (Fin w)))))

theorem preE7CharacterMainCoefficient_nonneg
    (lit : PreE7CharacterLiterature) {w : ℕ}
    (j : PreE7CharacterMenuIndex w) (b : ℕ) :
    0 ≤ preE7CharacterMainCoefficient lit j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7CharacterMenuCertificate lit j).coefficient_nonneg b)

theorem preE7CharacterTailCoefficient_nonneg
    (lit : PreE7CharacterLiterature) {w : ℕ}
    (j : PreE7CharacterMenuIndex w) (b : ℕ) :
    0 ≤ preE7CharacterTailCoefficient lit j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7CharacterMenuCertificate lit j).tail_nonneg b)

theorem preE7CharacterMainCoefficient_bound
    (lit : PreE7CharacterLiterature) {w : ℕ}
    (j : PreE7CharacterMenuIndex w) (b : ℕ) :
    preE7CharacterMainCoefficient lit j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  unfold preE7CharacterMainCoefficient preE7CharacterMenuCertificate
  rw [preE7_characterCertificate_eq]
  exact (preE7CharacterMenuSource j).main_total_bound b

theorem preE7CharacterTailCoefficient_bound
    (lit : PreE7CharacterLiterature) {w : ℕ}
    (j : PreE7CharacterMenuIndex w) (b : ℕ) :
    preE7CharacterTailCoefficient lit j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  unfold preE7CharacterTailCoefficient preE7CharacterMenuCertificate
  rw [preE7_characterCertificate_eq]
  exact (preE7CharacterMenuSource j).tail_total_bound b

theorem preE7CharacterMenuIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7CharacterMenuIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  let q : ℝ := Nat.card PreE7CharacterFamily
  refine ⟨q * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have hsub : Nat.card (PreE7CharacterMenuIndex w) ≤
      Nat.card (PreE7CharacterFamily × PreE7NonPairActionClass w) :=
    Finite.card_subtype_le _
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  have hprod : (Nat.card (PreE7CharacterMenuIndex w) : ℝ) ≤
      q * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    calc
      _ ≤ (Nat.card (PreE7CharacterFamily ×
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

theorem preE7CharacterMainEnvelope (lit : PreE7CharacterLiterature) :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7CharacterMainCoefficient lit (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7CharacterMainCoefficient_bound lit j (n - w))

theorem preE7CharacterTailEnvelope (lit : PreE7CharacterLiterature) :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7CharacterTailCoefficient lit (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7CharacterTailCoefficient_bound lit j (n - w))

theorem preE7CharacterMainMenuMass
    (lit : PreE7CharacterLiterature)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7CharacterMainCoefficient lit (w := w) j b)
      (fun w j => preE7CharacterMenuNormalizer (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7CharacterMainCoefficient_nonneg lit j b)
    (fun _ j => preE7CharacterMenuNormalizer_one_le j)
    (preE7CharacterMenuIndex_subquadratic hLMM)
    (preE7CharacterMainEnvelope lit)

theorem preE7CharacterTailMenuMass
    (lit : PreE7CharacterLiterature)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7CharacterTailCoefficient lit (w := w) j b)
      (fun w j => preE7CharacterMenuNormalizer (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7CharacterTailCoefficient_nonneg lit j b)
    (fun _ j => preE7CharacterMenuNormalizer_one_le j)
    (preE7CharacterMenuIndex_subquadratic hLMM)
    (preE7CharacterTailEnvelope lit)

theorem preE7CharacterParameters (lit : PreE7CharacterLiterature) :
    GrowingQuotientParameterBound preE7CharacterRho
        (fun w j => (preE7CharacterMenuCertificate lit (w := w) j).v)
        (fun w j => (preE7CharacterMenuCertificate lit (w := w) j).eta)
        (fun w j => (preE7CharacterMenuCertificate lit (w := w) j).delta)
        (fun w j => (preE7CharacterMenuCertificate lit (w := w) j).cutoff)
        (fun w j => (preE7CharacterMenuCertificate lit (w := w) j).alpha) ∧
      ∀ w j, (preE7CharacterMenuCertificate lit (w := w) j).theta ≤
        (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  apply growingQuotientParameterBound_of_entryParameters
  intro w j
  exact (preE7_characterCertificate_numerics j.1.1.1 j.1.1.2 w j.1.2
    (preE7CharacterMenuSource j).source lit).parameters

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
