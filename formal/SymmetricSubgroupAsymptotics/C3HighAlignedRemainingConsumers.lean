import SymmetricSubgroupAsymptotics.C3AlignedOwnerRefinement
import SymmetricSubgroupAsymptotics.C3NaturalA4AlignedLocal
import SymmetricSubgroupAsymptotics.C3DegreeSixAlignedLocal
import SymmetricSubgroupAsymptotics.C3DegreeTwelveAlignedLocal

/-!
# The four remaining aligned numerical consumers

The aligned branch refinement has six intrinsic alternatives.  The ternary
p-group and prime-base alternatives are closed separately.  The remaining
four are the natural-`A4` packet, the degree-six odd-index-two owner, the
degree-six cyclic binary-module owner, and the degree-twelve binary-nine
owner.  Each receives a nonnegative exponentially decaying local row on the
exact aligned canonical family:

* natural `A4`: the family is empty, with coefficient zero;
* degree six: the degree-six row, uniformly over both owners;
* binary nine: the mixed degree-twelve row, using the retained source
  pattern.

The degree-six quotients use the Kovács--Praeger abelianization bound as an
explicit hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The four remaining intrinsic alternatives of the aligned owner
refinement. -/
def C3HighAlignedRemainingRefinement {w : ℕ} (k : C3PhysicalOwnerKind)
    (U : Subgroup (Equiv.Perm (Fin w))) : Prop :=
  match k with
  | .ternaryPGroup => False
  | .naturalA4 => IsNaturalA4Action U (Fin w)
  | .degreeSix =>
      Nonempty (C1OddIndexTwoOwnerWitness U) ∨
      Nonempty (C1CyclicBinaryModuleOwnerWitness U)
  | .degreeTwelve => IsC1BinaryNineTopOwner U (Fin w)

/-- An aligned cell whose intrinsic owner is one of the four remaining
consumers. -/
def RemainingAlignedConsumer (j : C3HighAlignedFirstOwnerIndex) : Prop :=
  C3HighAlignedRemainingRefinement (c3PhysicalOwnerKindEquiv j.1.2.1)
    (c3HighAlignedFirstOwnerAction j)

/-- Every aligned refinement is a closed ternary p-group or prime-base
alternative, or one of the four remaining consumers. -/
theorem C3HighAlignedBranchRefinement.closed_or_remaining
    {j : C3HighAlignedFirstOwnerIndex} (h : C3HighAlignedBranchRefinement j) :
    (c3PhysicalOwnerKindEquiv j.1.2.1 = .ternaryPGroup ∧
        IsPGroup 3 (c3HighAlignedFirstOwnerAction j)) ∨
      (c3PhysicalOwnerKindEquiv j.1.2.1 = .degreeTwelve ∧
        IsC1TernaryPrimeBaseOwner (c3HighAlignedFirstOwnerAction j)) ∨
      RemainingAlignedConsumer j := by
  unfold C3HighAlignedBranchRefinement at h
  unfold RemainingAlignedConsumer
  generalize c3PhysicalOwnerKindEquiv j.1.2.1 = k at h ⊢
  cases k with
  | ternaryPGroup => exact Or.inl ⟨rfl, h⟩
  | naturalA4 => exact Or.inr (Or.inr h)
  | degreeSix => exact Or.inr (Or.inr h)
  | degreeTwelve =>
      rcases h with h | h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (Or.inr h)

/-- A nonnegative exponentially decaying local row on one aligned cell. -/
def C3HighAlignedLocalRow (j : C3HighAlignedFirstOwnerIndex) : Prop :=
  ∃ g : ℕ → ℝ, (∀ b, 0 ≤ g b) ∧
    (∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ b : ℕ in atTop, g b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ))) ∧
    ∀ (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        g (n - c3HighAlignedFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j)

/-- Every earlier numerical row with a nonnegative constant is a local row. -/
theorem C3HighAlignedLocalRow.of_kernel (j : C3HighAlignedFirstOwnerIndex)
    (r : C1EarlierRow) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - c3HighAlignedFirstOwnerWidth j) r D
            (Nat.card (Subgroup.normalizer
              (c3HighAlignedFirstOwnerAction j :
                Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j)) :
    C3HighAlignedLocalRow j := by
  have ha : (0 : ℝ) < (Nat.card (Subgroup.normalizer
      (c3HighAlignedFirstOwnerAction j :
        Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨C, hC, hev⟩ := c1EarlierKernel_eventually r hD ha
  exact ⟨fun b => c1EarlierKernel b r D _, fun b => c1EarlierKernel_nonneg b r hD ha,
    ⟨C, 1 / 36, hC, by norm_num, hev⟩, h⟩

/-- The natural-`A4` aligned cell has the zero local row. -/
theorem c3HighAligned_naturalA4_localRow (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 = C3PhysicalOwnerKind.naturalA4) :
    C3HighAlignedLocalRow j :=
  ⟨fun _ => 0, fun _ => le_rfl,
    ⟨1, 1, one_pos, one_pos, Filter.Eventually.of_forall fun b => by
      show (0 : ℝ) ≤ 1 * (2 : ℝ) ^ (-1 * (b : ℝ))
      positivity⟩,
    fun n hn => c3HighAligned_naturalA4_local_bound j hkind n hn⟩

/-- Each remaining aligned consumer has a local row. -/
theorem c3HighAligned_remaining_localRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighAlignedFirstOwnerIndex) (hj : RemainingAlignedConsumer j) :
    C3HighAlignedLocalRow j := by
  have hj' : C3HighAlignedRemainingRefinement (c3PhysicalOwnerKindEquiv j.1.2.1)
      (c3HighAlignedFirstOwnerAction j) := hj
  cases hk : c3PhysicalOwnerKindEquiv j.1.2.1 with
  | ternaryPGroup =>
      rw [hk] at hj'
      exact (hj' : False).elim
  | naturalA4 => exact c3HighAligned_naturalA4_localRow j hk
  | degreeSix =>
      obtain ⟨D, hD, h⟩ := c3HighAligned_degreeSix_local_bound hPrimitive hKP j hk
      exact C3HighAlignedLocalRow.of_kernel j .degreeSix D hD h
  | degreeTwelve =>
      obtain ⟨r, D, hD, h⟩ :=
        c3HighAligned_degreeTwelve_local_bound hChief hWeight hPrimitive h18 j hk
      exact C3HighAlignedLocalRow.of_kernel j r D hD h

/-- The four remaining aligned numerical consumers, in the exact local form
consumed by `c3PhysicalStructuralOwner_alignedExponentialForwardEstimate`. -/
theorem c3HighAligned_remainingConsumers_local
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    ∃ f : C3HighAlignedFirstOwnerIndex → ℕ → ℝ,
      (∀ j b, 0 ≤ f j b) ∧
      (∀ j, RemainingAlignedConsumer j →
        ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
          ∀ᶠ b : ℕ in atTop, f j b ≤ C * 2 ^ (-κ * (b : ℝ))) ∧
      (∀ j, RemainingAlignedConsumer j →
        ∀ n (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
          (Nat.card (FusionWidthCanonicalFamily (c3HighAlignedFirstOwnerAction j) hn
            (c3HighAlignedFirstOwnerPredicate j
              (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
              exactBenchmark n
            ≤ f j (n - c3HighAlignedFirstOwnerWidth j) *
                ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j)) := by
  have hrow := c3HighAligned_remaining_localRow hChief hWeight hPrimitive h18 hKP
  refine ⟨fun j => if h : RemainingAlignedConsumer j then Classical.choose (hrow j h)
      else fun _ => 0, fun j b => ?_, fun j hj => ?_, fun j hj n hn => ?_⟩
  · by_cases h : RemainingAlignedConsumer j
    · simp only [dif_pos h]
      exact (Classical.choose_spec (hrow j h)).1 b
    · simp only [dif_neg h]
      exact le_rfl
  · simp only [dif_pos hj]
    exact (Classical.choose_spec (hrow j hj)).2.1
  · simp only [dif_pos hj]
    exact (Classical.choose_spec (hrow j hj)).2.2 n hn

/-- The remaining consumers drop into the aligned forward continuation: with
local rows for the ternary p-group alternative, the prime-base rows and the
four remaining consumers close every aligned cell. -/
theorem c3PhysicalStructuralOwner_alignedExponentialForwardEstimate_nonempty
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hTernary : ∀ j : C3HighAlignedFirstOwnerIndex,
      c3PhysicalOwnerKindEquiv j.1.2.1 = C3PhysicalOwnerKind.ternaryPGroup →
        C3HighAlignedLocalRow j) :
    Nonempty (OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio) := by
  obtain ⟨f, hf0, hfdecay, hflocal⟩ :=
    c3HighAligned_remainingConsumers_local hChief hWeight hPrimitive h18 hKP
  have hclosed : ∀ j, ¬ RemainingAlignedConsumer j → C3HighAlignedLocalRow j := by
    intro j hj
    rcases (c3HighAligned_branchRefinement hChief hWeight hPrimitive h18 j).closed_or_remaining
      with ⟨hk, _⟩ | ⟨hk, ⟨W⟩⟩ | h
    · exact hTernary j hk
    · exact C3HighAlignedLocalRow.of_kernel j .degreeTwelve _
        (Finset.sum_nonneg (fun N _ => mul_nonneg (Nat.cast_nonneg _)
          (le_trans zero_le_one (le_max_left _ _))))
        (c3HighAligned_primeBase_local_bound j hk W)
    · exact absurd h hj
  choose g hg0 hgdecay hglocal using hclosed
  let F : C3HighAlignedFirstOwnerIndex → ℕ → ℝ := fun j =>
    if h : RemainingAlignedConsumer j then f j else g j h
  refine ⟨c3PhysicalStructuralOwner_alignedExponentialForwardEstimate
    hChief hWeight hPrimitive h18 F (fun j b => ?_) (fun j => ?_) (fun j n hn => ?_)⟩
  · by_cases h : RemainingAlignedConsumer j
    · simp only [F, dif_pos h]
      exact hf0 j b
    · simp only [F, dif_neg h]
      exact hg0 j h b
  · by_cases h : RemainingAlignedConsumer j
    · simp only [F, dif_pos h]
      exact hfdecay j h
    · simp only [F, dif_neg h]
      exact hgdecay j h
  · by_cases h : RemainingAlignedConsumer j
    · simp only [F, dif_pos h]
      exact hflocal j h n hn
    · simp only [F, dif_neg h]
      exact hglocal j h n hn

end SymmetricSubgroupAsymptotics

end
