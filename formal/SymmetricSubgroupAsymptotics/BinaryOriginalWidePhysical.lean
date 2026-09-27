import SymmetricSubgroupAsymptotics.BinaryOriginalZeroCutEntry
import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts
import SymmetricSubgroupAsymptotics.FusionDirectPhysicalUnion

/-!
# Physical installation of the complete original wide row

The sector consists of original subgroups with an actual binary orbit of
degree at least 4096. Its complement is unrestricted. One realized pairing
is chosen for each original action representative, and every original normal
uses its proved zero cut. This subfamily injects into the complete accepted
menu, whose extra entries are used only as nonnegative numerical majorants.

No class-bound input, coarse subgroup-growth estimate, physical-cover
assumption or weighted-menu estimate is a premise of the recurrence.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryOriginalWidePhysical

local instance physicalOriginalNormal {G : Type*} [Group G]
    (N : {N : Subgroup G // N.Normal}) : N.1.Normal := N.2

/-- The checked uniform zero-cut range, stated in the actual half-width. -/
def Admissible (h : ℕ) : Prop := h = 2^(Nat.log 2 h) ∧ 11 ≤ Nat.log 2 h

theorem admissible_ge {h : ℕ} (hh : Admissible h) : 32 ≤ h := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh.2
  have hb : 32 ≤ 2^11 := by norm_num
  exact hb.trans (hp.trans_eq hh.1.symm)

/-- Intrinsic unmarked sector. Only the selected orbit image is binary. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ h : ℕ, Admissible h ∧ ∃ x : Fin n,
    Nat.card (MulAction.orbit H x) = 2*h ∧
      IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x)}

/-- Each included width fits in the actual ambient point set. -/
def widths (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun h => Admissible h ∧ 2*h ≤ n)

theorem width_properties {n : ℕ} (h : widths n) : Admissible h.1 ∧ 2*h.1 ≤ n :=
  (Finset.mem_filter.mp h.2).2

abbrev Action (n : ℕ) := Σ h : widths n, BinaryTransitiveActionClass (Fin (2*h.1))

def action {n : ℕ} (j : Action n) : Subgroup (Equiv.Perm (Fin (2*j.1.1))) :=
  j.2.representative

/-- One actual pairing, fixed before the complement or its degree is used. -/
def pairing {h : ℕ} (hh : Admissible h)
    (i : BinaryTransitiveActionClass (Fin (2*h))) :
    RealizedPairing i.representative (Fin (2^(Nat.log 2 h))) := by
  apply Classical.choice
  apply transitiveBinaryRealizedPairing_nonempty (Nat.log 2 h)
    i.representative i.representative_isPGroup
  rw [Nat.card_fin, pow_succ]
  have hp := hh.1
  omega

abbrev Axis (h : ℕ) := Σ i : BinaryTransitiveActionClass (Fin (2*h)),
  {N : Subgroup i.representative // N.Normal}

/-- The literal zero entry attached to every original action/normal pair. -/
def zeroEntry {h : ℕ} (hh : Admissible h) (j : Axis h) : BinaryOriginalWideEntry h :=
  BinaryOriginalZeroCutEntry.acceptedEntry h j.1 (pairing hh j.1) j.2 hh.1 hh.2

theorem zeroEntry_injective {h : ℕ} (hh : Admissible h) :
    Function.Injective (zeroEntry hh) := by
  intro j j' he
  exact congrArg (fun z : BinaryOriginalWideEntry h =>
    (⟨z.1.1,z.1.2.2.1⟩ : Axis h)) he

/-- Actual original orbit charts supply the complete representative cover. -/
theorem cover (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ physicalFamily n) :
    ∃ j : Action n, H ∈ FusionCanonicalFamily (action j)
      (width_properties j.1).2 (fun _ => True) := by
  obtain ⟨h,hh,x,hw,hP⟩ := hH
  have hn := FusionActualOrbitCharts.degree_le H x hw
  have hmem : h ∈ widths n := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega),hh,hn⟩
  obtain ⟨i,hi⟩ := FusionOrbitRepresentativeCharts.exists_canonicalFamily H x hw hP hn
  exact ⟨⟨⟨h,hmem⟩,i⟩,hi⟩

def normalizedCount (m : ℕ) : ℝ := (subgroupCount m : ℝ)/exactBenchmark m

theorem normalizedCount_nonneg (m : ℕ) : 0 ≤ normalizedCount m :=
  div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos m).le

/-- The complete accepted entry's actual coefficient and target. -/
def entryWeight (n h : ℕ) (j : BinaryOriginalWideEntry h) : ℝ :=
  fusionDirectKernel (n-2*h) h (2*BinaryOriginalWideEntry.markerHalf h j)
    (BinaryOriginalWideEntry.cost h j) (BinaryOriginalWideEntry.divisor h j)
    (BinaryOriginalWideEntry.gap h j) *
      normalizedCount (n-2*h+2*BinaryOriginalWideEntry.markerHalf h j)

theorem entryWeight_nonneg (n h : ℕ) (j : BinaryOriginalWideEntry h) :
    0 ≤ entryWeight n h j :=
  mul_nonneg (fusionDirectKernel_nonneg _ _ _
    (BinaryOriginalWideEntry.cost_nonneg h j) (BinaryOriginalWideEntry.divisor_pos h j))
      (normalizedCount_nonneg _)

/-- The first-moment theorem is installed on every original normal,
using only its already checked zero-cut envelope and same-source moment. -/
theorem local_count_le {n h : ℕ} (hh : Admissible h) (hn : 2*h ≤ n)
    (i : BinaryTransitiveActionClass (Fin (2*h))) :
    (Nat.card (FusionCanonicalFamily i.representative hn (fun _ => True)) : ℝ)/
      exactBenchmark n ≤
        ∑ N : {N : Subgroup i.representative // N.Normal},
          entryWeight n h (zeroEntry hh ⟨i,N⟩) := by
  rw [fusionCanonicalFamily_card]
  let p := pairing hh i
  let v := fun N : {N : Subgroup i.representative // N.Normal} =>
    2*(BinaryOriginalZeroCutEntry.entry h i p N).markerHalf
  let D := fun N : {N : Subgroup i.representative // N.Normal} =>
    (BinaryOriginalZeroCutEntry.entry h i p N).cost
  let e := fun N : {N : Subgroup i.representative // N.Normal} =>
    (BinaryOriginalZeroCutEntry.entry h i p N).directGap h
  let Φ := fun (N : {N : Subgroup i.representative // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin (n-2*h)))) => p.chosenFrame.zeroCutMomentWeight N.1 J
  have henv : ∀ N J, fusionSurvivingEpiCount i.representative (fun _ => True) N J ≤
      fusionLocalFactor (n-2*h) h (v N) (D N) (e N)*Φ N J := by
    intro N J
    exact BinaryOriginalZeroCutEntry.original_survivingEpiCount_le h i p N
      hh.1 hh.2 (fun _ => True) J
  have hm : ∀ N, (∑ J, Φ N J) ≤ (subgroupCount (n-2*h+v N) : ℝ) := by
    intro N
    have hmoment := BinaryOriginalZeroCutEntry.moment_le h i p N (n-2*h) 1 hh.1
    change (∑ J : Subgroup (Equiv.Perm (Fin (n-2*h))),
      p.chosenFrame.zeroCutMomentWeight N.1 J) ≤
        (subgroupCount (n-2*h+2*(BinaryOriginalZeroCutEntry.entry h i p N).markerHalf) : ℝ)
    rw [BinaryOriginalZeroCutEntry.prefix_eq h i p N hh.1 hh.2]
    simpa only [pow_one, one_mul] using hmoment
  have hb := fusionPhysical_direct_bound i.representative (n-2*h) (fun _ => True)
    (fun _ _ _ => trivial) v D e Φ (fun N =>
      (BinaryOriginalZeroCutEntry.entry h i p N).cost_nonneg) henv hm
  simp only [Nat.sub_add_cancel hn, entryWeight, normalizedCount,
    BinaryOriginalWideEntry.markerHalf, BinaryOriginalWideEntry.cost,
    BinaryOriginalWideEntry.divisor, BinaryOriginalWideEntry.gap,
    BinaryOriginalMenuEntry.divisor, zeroEntry, BinaryOriginalZeroCutEntry.acceptedEntry,
    BinaryOriginalZeroCutEntry.entry, p, v, D, e] at hb ⊢
  exact hb.trans_eq (Finset.sum_congr
    (by ext; simp only [Finset.mem_univ]) (fun _ _ => rfl))

/-- Selected zero entries have no duplicate labels. Extra accepted cuts
are only nonnegative terms in this numerical comparison. -/
theorem zero_sum_le (n h : ℕ) (hh : Admissible h) :
    (∑ i : BinaryTransitiveActionClass (Fin (2*h)),
      ∑ N : {N : Subgroup i.representative // N.Normal},
        entryWeight n h (zeroEntry hh ⟨i,N⟩)) ≤
      ∑ j : BinaryOriginalWideEntry h, entryWeight n h j := by
  have hs : (∑ i : BinaryTransitiveActionClass (Fin (2*h)),
      ∑ N : {N : Subgroup i.representative // N.Normal},
        entryWeight n h (zeroEntry hh ⟨i,N⟩)) =
      ∑ j : Axis h, entryWeight n h (zeroEntry hh j) := by
    apply Eq.trans ?_ (Fintype.sum_sigma
      (fun j : Axis h => entryWeight n h (zeroEntry hh j))).symm
    apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
    intro i _
    apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
    intro N _
    rfl
  rw [hs]
  calc
    _ = ∑ j ∈ Finset.univ.image (zeroEntry hh), entryWeight n h j :=
      (Finset.sum_image (zeroEntry_injective hh).injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => entryWeight_nonneg n h j)

def widthContribution (n h : ℕ) : ℝ :=
  if 32 ≤ h ∧ 2*h ≤ n then ∑ j : BinaryOriginalWideEntry h, entryWeight n h j else 0

theorem widthContribution_nonneg (n h : ℕ) : 0 ≤ widthContribution n h := by
  unfold widthContribution
  split_ifs
  · exact Finset.sum_nonneg (fun j _ => entryWeight_nonneg n h j)
  · exact le_rfl

/-- The complete row preserves each original summand at its actual target,
including different entries reaching the same target degree. -/
theorem row_weighted_sum (n : ℕ) :
    (∑ m ∈ Finset.range n, binaryOriginalWideRow n m*normalizedCount m) =
      ∑ h ∈ Finset.range (n+1), widthContribution n h := by
  unfold binaryOriginalWideRow fusionWideDirectRow widthContribution
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : 32 ≤ h ∧ 2*h ≤ n
  · simp only [if_pos hh]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have hp := BinaryOriginalWideEntry.prefix_le h j
    have ht : n-2*h+2*BinaryOriginalWideEntry.markerHalf h j < n := by omega
    rw [Finset.sum_eq_single (n-2*h+2*BinaryOriginalWideEntry.markerHalf h j)]
    · simp only [ite_true, entryWeight]
    · intro m _ hm
      simp only [if_neg (Ne.symm hm)]
    · simp only [Finset.mem_range.mpr ht, not_true_eq_false, false_implies]
  · simp only [if_neg hh, Finset.sum_const_zero]

/-- Actual unmarked growing-width sector recurrence. All representatives,
pairings, literal normals, weights and local bounds are supplied internally. -/
theorem direct_recurrence (n : ℕ) :
    (Nat.card (physicalFamily n) : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, binaryOriginalWideRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  have hc := fusionPhysicalUnion_card_le (physicalFamily n)
    (fun j : Action n => FusionCanonicalFamily (action j)
      (width_properties j.1).2 (fun _ => True)) (cover n)
  have hcR : (Nat.card (physicalFamily n) : ℝ) ≤
      ∑ j : Action n, (Nat.card (FusionCanonicalFamily (action j)
        (width_properties j.1).2 (fun _ => True)) : ℝ) := by exact_mod_cast hc
  calc
    _ ≤ (∑ j : Action n, (Nat.card (FusionCanonicalFamily (action j)
        (width_properties j.1).2 (fun _ => True)) : ℝ))/exactBenchmark n :=
      div_le_div_of_nonneg_right hcR (exactBenchmark_pos n).le
    _ = ∑ h : widths n, ∑ i : BinaryTransitiveActionClass (Fin (2*h.1)),
        (Nat.card (FusionCanonicalFamily i.representative
          (width_properties h).2 (fun _ => True)) : ℝ)/exactBenchmark n := by
      rw [Finset.sum_div, Fintype.sum_sigma]
      rfl
    _ ≤ ∑ h : widths n, ∑ i : BinaryTransitiveActionClass (Fin (2*h.1)),
        ∑ N : {N : Subgroup i.representative // N.Normal},
          entryWeight n h.1 (zeroEntry (width_properties h).1 ⟨i,N⟩) := by
      apply Finset.sum_le_sum
      intro h _
      exact Finset.sum_le_sum (fun i _ =>
        local_count_le (width_properties h).1 (width_properties h).2 i)
    _ ≤ ∑ h : widths n, ∑ j : BinaryOriginalWideEntry h.1, entryWeight n h.1 j :=
      Finset.sum_le_sum (fun h _ => zero_sum_le n h.1 (width_properties h).1)
    _ = ∑ h ∈ widths n, widthContribution n h := by
      calc
        _ = ∑ h : widths n, widthContribution n h.1 := by
          apply Finset.sum_congr rfl
          intro h _
          exact (if_pos ⟨admissible_ge (width_properties h).1,(width_properties h).2⟩).symm
        _ = _ := Finset.sum_coe_sort (widths n) (widthContribution n)
    _ ≤ ∑ h ∈ Finset.range (n+1), widthContribution n h :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun h _ _ => widthContribution_nonneg n h)
    _ = _ := (row_weighted_sum n).symm

/-- Arbitrary exclusions restrict the same original subgroup family by
literal inclusion. No relabelling invariance of the exclusion is needed. -/
theorem filtered_direct_recurrence (n : ℕ)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // P H.1} : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, binaryOriginalWideRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // P H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence n)

end SymmetricSubgroupAsymptotics.BinaryOriginalWidePhysical

end
