import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleNumerics
import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairMenuMassAggregation
import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage

/-!
# Complete ordinary semisimple menu

This is the shared numerical closure for `SS`, `SO`, `SNS`, and `NSAPRIM`.
`SNS2` is excluded because its binary quotient must retain the correlated
rank-tail moment; its all-width menu is proved separately.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

def IsPreE7OrdinarySemisimpleFamily
    (family : PreE7NoPairNoC3EarlierOwnerFamily) : Prop :=
  IsPreE7SemisimpleFamily family ∧ family ≠ .sns2

instance : DecidablePred IsPreE7OrdinarySemisimpleFamily := fun family =>
  inferInstanceAs (Decidable
    (IsPreE7SemisimpleFamily family ∧ family ≠ .sns2))

abbrev PreE7OrdinarySemisimpleFamily :=
  {family : PreE7NoPairNoC3EarlierOwnerFamily //
    IsPreE7OrdinarySemisimpleFamily family}

abbrev PreE7OrdinarySemisimpleMenuIndex (w : ℕ) :=
  {p : PreE7OrdinarySemisimpleFamily × PreE7NonPairActionClass w //
    Nonempty (SemisimpleCertificateSourceData p.1.1 w p.2)}

noncomputable instance preE7OrdinarySemisimpleMenuIndexFintype (w : ℕ) :
    Fintype (PreE7OrdinarySemisimpleMenuIndex w) :=
  Fintype.ofFinite (PreE7OrdinarySemisimpleMenuIndex w)

noncomputable def preE7OrdinarySemisimpleMenuSource {w : ℕ}
    (j : PreE7OrdinarySemisimpleMenuIndex w) :
    SemisimpleCertificateSourceData j.1.1.1 w j.1.2 :=
  Classical.choice j.2

private noncomputable def ordinarySemisimpleCertificate
    (hgen : PermutationSubgroupGeneratorBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7OrdinarySemisimpleFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : SemisimpleCertificateSourceData family w i) :
    PreE7EarlierActionComparatorCertificate family w i := by
  rcases hfamily with ⟨hsemisimple, hne⟩
  cases family
  all_goals first
    | exact absurd hsemisimple (by decide)
    | skip
  case ss => exact preE7_ssCertificate S
  case so => exact preE7_soCertificate hgen S
  case sns => exact preE7_snsCertificate hgen S
  case sns2 => exact absurd rfl hne
  case nsaprim => exact preE7_nsaprimCertificate S

noncomputable def preE7OrdinarySemisimpleMenuCertificate
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} (j : PreE7OrdinarySemisimpleMenuIndex w) :
    PreE7EarlierActionComparatorCertificate j.1.1.1 w j.1.2 :=
  ordinarySemisimpleCertificate hgen j.1.1.1 j.1.1.2
    (preE7OrdinarySemisimpleMenuSource j)

def preE7OrdinarySemisimpleMenuAction {w : ℕ}
    (j : PreE7OrdinarySemisimpleMenuIndex w) :=
  preE7NonPairAction w j.1.2

def preE7OrdinarySemisimpleMenuNormalizer {w : ℕ}
    (j : PreE7OrdinarySemisimpleMenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7OrdinarySemisimpleMenuAction j : Set (Equiv.Perm (Fin w))))

def preE7OrdinarySemisimpleCoefficient
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} (j : PreE7OrdinarySemisimpleMenuIndex w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7OrdinarySemisimpleMenuAction j)
    ((preE7OrdinarySemisimpleMenuCertificate hgen j).C b)

theorem preE7OrdinarySemisimpleMenuNormalizer_one_le {w : ℕ}
    (j : PreE7OrdinarySemisimpleMenuIndex w) :
    1 ≤ preE7OrdinarySemisimpleMenuNormalizer j := by
  unfold preE7OrdinarySemisimpleMenuNormalizer
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7OrdinarySemisimpleMenuAction j : Set (Equiv.Perm (Fin w)))))

theorem preE7OrdinarySemisimpleCoefficient_nonneg
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} (j : PreE7OrdinarySemisimpleMenuIndex w) (b : ℕ) :
    0 ≤ preE7OrdinarySemisimpleCoefficient hgen j b :=
  fusionAxisEnvelopeTotal_nonneg _ _
    ((preE7OrdinarySemisimpleMenuCertificate hgen j).coefficient_nonneg b)

private theorem source_total_bound
    (hgen : PermutationSubgroupGeneratorBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7OrdinarySemisimpleFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : SemisimpleCertificateSourceData family w i) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((ordinarySemisimpleCertificate hgen family hfamily S).C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  rcases hfamily with ⟨hsemisimple, hne⟩
  cases family
  all_goals first
    | exact absurd hsemisimple (by decide)
    | skip
  case ss => exact S.coefficient_total_bound b
  case so => exact S.down.coefficient_total_bound b
  case sns => exact S.coefficient_total_bound b
  case sns2 => exact absurd rfl hne
  case nsaprim => exact S.down.coefficient_total_bound b

private theorem source_tail_total_bound
    (hgen : PermutationSubgroupGeneratorBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7OrdinarySemisimpleFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : SemisimpleCertificateSourceData family w i) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((ordinarySemisimpleCertificate hgen family hfamily S).tailCoefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  rcases hfamily with ⟨hsemisimple, hne⟩
  cases family
  all_goals first
    | exact absurd hsemisimple (by decide)
    | skip
  case sns2 => exact absurd rfl hne
  all_goals
    simp [ordinarySemisimpleCertificate, preE7_ssCertificate,
      preE7_soCertificate, preE7_snsCertificate,
      preE7_nsaprimCertificate,
      PreE7SemisimpleDirectSourceData.certificate,
      PreE7SoOrderSourceData.certificate,
      PreE7NsaprimActionCertificate.certificate,
      fusionAxisEnvelopeTotal]
  all_goals positivity

private theorem ordinarySemisimpleEntryParameters
    (hgen : PermutationSubgroupGeneratorBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7OrdinarySemisimpleFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : SemisimpleCertificateSourceData family w i) :
    let C := ordinarySemisimpleCertificate hgen family hfamily S
    PreE7CharacterEntryParameters preE7CharacterRho w C.v C.eta C.delta
      C.cutoff C.alpha C.theta := by
  rcases hfamily with ⟨hsemisimple, hne⟩
  cases family
  all_goals first
    | exact absurd hsemisimple (by decide)
    | skip
  case ss => exact S.entryParameters
  case so => exact S.down.entryParameters
  case sns => exact S.entryParameters
  case sns2 => exact absurd rfl hne
  case nsaprim => exact S.down.entryParameters

theorem preE7OrdinarySemisimpleCoefficient_bound
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} (j : PreE7OrdinarySemisimpleMenuIndex w) (b : ℕ) :
    preE7OrdinarySemisimpleCoefficient hgen j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  exact source_total_bound hgen j.1.1.1 j.1.1.2
    (preE7OrdinarySemisimpleMenuSource j) b

theorem preE7OrdinarySemisimpleMenuIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7OrdinarySemisimpleMenuIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  let q : ℝ := Nat.card PreE7OrdinarySemisimpleFamily
  refine ⟨q * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have hsub : Nat.card (PreE7OrdinarySemisimpleMenuIndex w) ≤
      Nat.card (PreE7OrdinarySemisimpleFamily ×
        PreE7NonPairActionClass w) := Finite.card_subtype_le _
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  have hprod : (Nat.card (PreE7OrdinarySemisimpleMenuIndex w) : ℝ) ≤
      q * (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    calc
      _ ≤ (Nat.card (PreE7OrdinarySemisimpleFamily ×
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

theorem preE7OrdinarySemisimpleEnvelope
    (hgen : PermutationSubgroupGeneratorBound) :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7OrdinarySemisimpleCoefficient hgen
        (w := w) j b) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [zero_mul, zero_add, one_mul, hwb, Nat.cast_add,
    Nat.cast_ofNat] using
    (preE7OrdinarySemisimpleCoefficient_bound hgen j (n - w))

theorem preE7OrdinarySemisimpleMenuMass
    (hgen : PermutationSubgroupGeneratorBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3
      (fun w j b => preE7OrdinarySemisimpleCoefficient hgen
        (w := w) j b)
      (fun w j => preE7OrdinarySemisimpleMenuNormalizer (w := w) j) :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (fun _ j b => preE7OrdinarySemisimpleCoefficient_nonneg hgen j b)
    (fun _ j => preE7OrdinarySemisimpleMenuNormalizer_one_le j)
    (preE7OrdinarySemisimpleMenuIndex_subquadratic hLMM)
    (preE7OrdinarySemisimpleEnvelope hgen)

theorem preE7OrdinarySemisimpleParameters
    (hgen : PermutationSubgroupGeneratorBound) :
    GrowingQuotientParameterBound preE7CharacterRho
        (fun w j => (preE7OrdinarySemisimpleMenuCertificate
          hgen (w := w) j).v)
        (fun w j => (preE7OrdinarySemisimpleMenuCertificate
          hgen (w := w) j).eta)
        (fun w j => (preE7OrdinarySemisimpleMenuCertificate
          hgen (w := w) j).delta)
        (fun w j => (preE7OrdinarySemisimpleMenuCertificate
          hgen (w := w) j).cutoff)
        (fun w j => (preE7OrdinarySemisimpleMenuCertificate
          hgen (w := w) j).alpha) ∧
      ∀ w j, (preE7OrdinarySemisimpleMenuCertificate hgen (w := w) j).theta ≤
        (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  apply growingQuotientParameterBound_of_entryParameters
  intro w j
  exact ordinarySemisimpleEntryParameters hgen j.1.1.1 j.1.1.2
    (preE7OrdinarySemisimpleMenuSource j)

/-- One ordinary semisimple source supplies the exact numerically complete
package used by the mixed catalogue. -/
noncomputable def preE7OrdinarySemisimpleNumericalPackage
    (hgen : PermutationSubgroupGeneratorBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7OrdinarySemisimpleFamily family)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (source : SemisimpleCertificateSourceData family w i) :
    PreE7EarlierNumericalPackage family w i :=
  .ofComparator
    (ordinarySemisimpleCertificate hgen family hfamily source)
    (ordinarySemisimpleEntryParameters hgen family hfamily source)
    (source_total_bound hgen family hfamily source)
    (source_tail_total_bound hgen family hfamily source)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
