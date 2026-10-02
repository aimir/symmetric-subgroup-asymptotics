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

noncomputable def preE7OrdinarySemisimpleNsaprimCertificate {w : ℕ}
    (j : PreE7OrdinarySemisimpleMenuIndex w)
    (h : j.1.1.1 = .nsaprim) :
    PreE7NsaprimActionCertificate w j.1.2 := by
  have S := preE7OrdinarySemisimpleMenuSource j
  rw [h] at S
  exact S.down

/-- The whole NSAPRIM part of the ordinary semisimple menu is finite: its
source certificate itself records `w ≤ 1024`. -/
abbrev PreE7BoundedNsaprimMenuIndex :=
  Σ fw : Fin 1025,
    {j : PreE7OrdinarySemisimpleMenuIndex fw.1 // j.1.1.1 = .nsaprim}

noncomputable def preE7BoundedNsaprimCertificate
    (z : PreE7BoundedNsaprimMenuIndex) :
    PreE7NsaprimActionCertificate z.1.1 z.2.1.1.2 := by
  exact preE7OrdinarySemisimpleNsaprimCertificate z.2.1 z.2.2

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
  if hns : j.1.1.1 = .nsaprim then
    fusionAxisEnvelopeTotal (preE7NonPairAction w j.1.2)
      (fun _ =>
        (preE7OrdinarySemisimpleNsaprimCertificate j hns).coefficient b)
  else
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
  by
    unfold preE7OrdinarySemisimpleCoefficient
    split_ifs with hns
    · exact fusionAxisEnvelopeTotal_nonneg _ _
        (fun _ => (preE7OrdinarySemisimpleNsaprimCertificate j hns).coefficient_nonneg b)
    · exact fusionAxisEnvelopeTotal_nonneg _ _
        ((preE7OrdinarySemisimpleMenuCertificate hgen j).coefficient_nonneg b)

private theorem source_total_bound
    (hgen : PermutationSubgroupGeneratorBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7OrdinarySemisimpleFamily family)
    (hnotns : family ≠ .nsaprim)
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
  case nsaprim => exact absurd rfl hnotns

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

theorem preE7OrdinarySemisimpleCoefficient_bound_of_not_nsaprim
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} (j : PreE7OrdinarySemisimpleMenuIndex w)
    (hne : j.1.1.1 ≠ .nsaprim) (b : ℕ) :
    preE7OrdinarySemisimpleCoefficient hgen j b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  unfold preE7OrdinarySemisimpleCoefficient
  rw [dif_neg hne]
  exact source_total_bound hgen j.1.1.1 j.1.1.2 hne
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

private theorem shifted_natPow_le_width_logSquared
    (p n w : ℕ) (hw : w ∈ Finset.Ico 3 (n + 1)) :
    (1 + ((n - w : ℕ) : ℝ)) ^ p ≤
      (2 : ℝ) ^
        ((p : ℝ) * w * Real.log ((n : ℝ) + 2) ^ 2) := by
  let X : ℝ := (n : ℝ) + 2
  have hww := Finset.mem_Ico.mp hw
  have hX4 : (4 : ℝ) ≤ X := by
    have : 3 ≤ n := hww.1.trans (by omega)
    dsimp [X]
    exact_mod_cast (show 4 ≤ n + 2 by omega)
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX4
  have hlogtwo : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogone : 1 ≤ Real.log X := by
    have hm : Real.log (4 : ℝ) ≤ Real.log X :=
      Real.log_le_log (by norm_num) hX4
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hm
    norm_num at hm
    linarith
  have hlogb : Real.logb 2 X ≤ 2 * Real.log X := by
    rw [Real.logb]
    have hden : 0 < Real.log 2 := hlogtwo.trans' (by norm_num)
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (zero_le_one.trans hlogone)
      (sub_nonneg.mpr hlogtwo.le)]
  have hwidth : 2 * Real.log X ≤ (w : ℝ) * Real.log X ^ 2 := by
    have hwR : (3 : ℝ) ≤ w := by exact_mod_cast hww.1
    nlinarith [sq_nonneg (Real.log X - 1)]
  have hexp : (p : ℝ) * Real.logb 2 X ≤
      (p : ℝ) * w * Real.log X ^ 2 := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hlogb.trans hwidth) (Nat.cast_nonneg p))
  have hbase : (1 : ℝ) + (n - w : ℕ) ≤ X := by
    dsimp [X]
    exact_mod_cast (show 1 + (n - w) ≤ n + 2 by omega)
  calc
    (1 + ((n - w : ℕ) : ℝ)) ^ p ≤ X ^ p := by gcongr
    _ = X ^ (p : ℝ) := by rw [Real.rpow_natCast]
    _ = ((2 : ℝ) ^ Real.logb 2 X) ^ (p : ℝ) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) hXpos]
    _ = (2 : ℝ) ^ (Real.logb 2 X * p) := by
      rw [← Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ ((p : ℝ) * Real.logb 2 X) := by
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

theorem preE7OrdinarySemisimpleEnvelope
    (hgen : PermutationSubgroupGeneratorBound) :
    LinearLogSquaredMenuNumeratorBound 3
      (fun w j b => preE7OrdinarySemisimpleCoefficient hgen
        (w := w) j b) := by
  obtain ⟨K, hK⟩ := Finite.exists_le
    (fun z : PreE7BoundedNsaprimMenuIndex =>
      (preE7BoundedNsaprimCertificate z).polynomialConstant)
  obtain ⟨p, hp⟩ := Finite.exists_le
    (fun z : PreE7BoundedNsaprimMenuIndex =>
      (preE7BoundedNsaprimCertificate z).polynomialDegree)
  refine ⟨max 1 K, 0, 16 + p, by positivity, by norm_num, by positivity, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  by_cases hns : j.1.1.1 = .nsaprim
  · let C : PreE7NsaprimActionCertificate w j.1.2 :=
      preE7OrdinarySemisimpleNsaprimCertificate j hns
    let fw : Fin 1025 := ⟨w, by
      have := C.width_upper
      omega⟩
    let z : PreE7BoundedNsaprimMenuIndex := ⟨fw, ⟨j, hns⟩⟩
    have hCeq : preE7BoundedNsaprimCertificate z = C := by
      rfl
    have hKC : C.polynomialConstant ≤ max 1 K := by
      have hz := hK z
      rw [hCeq] at hz
      exact hz.trans (le_max_right _ _)
    have hpC : C.polynomialDegree ≤ p := by
      have hz := hp z
      rw [hCeq] at hz
      exact hz
    have hpoly := C.coefficient_total_le_polynomial (n - w)
    have hbase : (1 : ℝ) ≤ 1 + (n - w : ℕ) := by
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hpow : (1 + ((n - w : ℕ) : ℝ)) ^ C.polynomialDegree ≤
        (1 + ((n - w : ℕ) : ℝ)) ^ p :=
      pow_le_pow_right₀ hbase hpC
    have hshift := shifted_natPow_le_width_logSquared p n w hw
    have hmain : preE7OrdinarySemisimpleCoefficient hgen j (n - w) ≤
        (max 1 K) *
          (2 : ℝ) ^ ((p : ℝ) * w * Real.log ((n : ℝ) + 2) ^ 2) := by
      calc
        preE7OrdinarySemisimpleCoefficient hgen j (n - w) ≤
            C.polynomialConstant *
              (1 + ((n - w : ℕ) : ℝ)) ^ C.polynomialDegree := by
          unfold preE7OrdinarySemisimpleCoefficient
          rw [dif_pos hns]
          exact hpoly
        _ ≤ (max 1 K) * (1 + ((n - w : ℕ) : ℝ)) ^ p :=
          mul_le_mul hKC hpow (by positivity) (by positivity)
        _ ≤ (max 1 K) *
            (2 : ℝ) ^ ((p : ℝ) * w * Real.log ((n : ℝ) + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hshift (by positivity)
    exact hmain.trans (by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlogsq : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
      have hw0 : (0 : ℝ) ≤ w := by positivity
      norm_num
      nlinarith)
  · have hold := preE7OrdinarySemisimpleCoefficient_bound_of_not_nsaprim
        hgen j hns (n - w)
    have hlogsq : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
    have hw0 : (0 : ℝ) ≤ w := by positivity
    calc
      preE7OrdinarySemisimpleCoefficient hgen j (n - w) ≤
          (2 : ℝ) ^
            (16 * (w : ℝ) * Real.log ((w + (n - w) + 2 : ℕ) : ℝ) ^ 2) :=
        hold
      _ ≤ (max 1 K) *
          (2 : ℝ) ^
            ((16 + (p : ℝ)) * w * Real.log ((n : ℝ) + 2) ^ 2) := by
        rw [hwb]
        have hpow : (2 : ℝ) ^
              (16 * (w : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) ^ 2) ≤
            (2 : ℝ) ^
              ((16 + (p : ℝ)) * w * Real.log ((n : ℝ) + 2) ^ 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          norm_num
          have hp0 : (0 : ℝ) ≤ p := by positivity
          nlinarith [mul_nonneg hp0 (mul_nonneg hw0 hlogsq)]
        exact hpow.trans (by
          nth_rewrite 1 [← one_mul ((2 : ℝ) ^ _)]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = (max 1 K) *
          (2 : ℝ) ^
            (0 * w + (16 + (p : ℝ)) * w * Real.log ((n : ℝ) + 2) ^ 2) := by
        congr 2
        ring

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
    PreE7EarlierNumericalPackage family w i := by
  by_cases hns : family = .nsaprim
  · subst family
    have hcert :
        ordinarySemisimpleCertificate hgen .nsaprim hfamily source =
          source.down.certificate := by
      rcases hfamily with ⟨hsemisimple, hnotsns2⟩
      rfl
    have hpoly : ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
        fusionAxisEnvelopeTotal (preE7NonPairAction w i)
          ((ordinarySemisimpleCertificate hgen .nsaprim hfamily source).C b) ≤
            K * (1 + (b : ℝ)) ^ p := by
      rw [hcert]
      exact source.down.coefficient_total_polynomial
    exact .ofPolynomialComparator
      (ordinarySemisimpleCertificate hgen .nsaprim hfamily source)
      (ordinarySemisimpleEntryParameters hgen .nsaprim hfamily source)
      source.down.width_upper hpoly
      (source_tail_total_bound hgen .nsaprim hfamily source)
  · exact .ofComparator
      (ordinarySemisimpleCertificate hgen family hfamily source)
      (ordinarySemisimpleEntryParameters hgen family hfamily source)
      (source_total_bound hgen family hfamily hns source)
      (source_tail_total_bound hgen family hfamily source)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
