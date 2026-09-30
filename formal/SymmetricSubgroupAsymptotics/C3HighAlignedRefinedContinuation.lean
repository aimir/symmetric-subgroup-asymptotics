import SymmetricSubgroupAsymptotics.C3PhysicalOwnerAlignedContinuation
import SymmetricSubgroupAsymptotics.C3C1PatternAlignedCoverage
import SymmetricSubgroupAsymptotics.C1DegreeNineSourcePatternRelabel

/-!
# The aligned high-C3 continuation without the degree-three ternary cell

A width-three aligned cell whose first owner is the ternary p-group branch
is an indexing artefact.  The physical cover never needs it: on the actual
selected nested carrier, full projection onto the displayed regular `C3`
makes that triple an orbit, and the retained one-`C3` pattern forbids a
second width-three ternary orbit.  The exclusion is derived there, before
the carrier is forgotten into an enlarged canonical cell; it is not a claim
that the enlarged width-three cell is empty.

The refined index keeps every other aligned cell, and the cover and the
forward-estimate assembly are rebuilt on it.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The removed indexing artefact: a width-three aligned cell whose first
owner is the ternary p-group branch. -/
def C3HighAlignedDegreeThreeTernary (j : C3HighAlignedFirstOwnerIndex) : Prop :=
  c3HighAlignedFirstOwnerWidth j = 3 ∧
    c3PhysicalOwnerKindEquiv j.1.2.1 = C3PhysicalOwnerKind.ternaryPGroup

/-- The aligned index with the width-three ternary p-group cells removed. -/
abbrev C3HighRefinedAlignedIndex :=
  {j : C3HighAlignedFirstOwnerIndex // ¬ C3HighAlignedDegreeThreeTernary j}

/-- The width of a refined aligned cell. -/
def c3HighRefinedWidth (j : C3HighRefinedAlignedIndex) : ℕ :=
  c3HighAlignedFirstOwnerWidth j.1

theorem c3HighRefinedWidth_pos (j : C3HighRefinedAlignedIndex) :
    0 < c3HighRefinedWidth j :=
  c3HighAlignedFirstOwnerWidth_pos j.1

/-- The complete high-C3 owner is covered by refined aligned cells.  The
selected nested carrier is kept until the width-three ternary alternative
has been excluded on it. -/
theorem c3PhysicalStructuralOwner_refinedAlignedCover
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 27 ≤ n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : G ∈ C3PhysicalStructuralOwnerSet n) :
    ∃ j : C3HighRefinedAlignedIndex,
      G ∈ FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j.1)
        (c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le n hn j.1)
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1)) := by
  obtain ⟨ownerEligible, hEligible⟩ :=
    c3PhysicalStructuralBranchMenu_cover
      hChief hWeight hPrimitive h18 hG.2.1
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (c3PatternStructuralBranchMenu n) G
      ⟨ownerEligible, hEligible, hG.2.2⟩
  rcases howner.1.1 with ⟨b, e, H, hphysical, hfull, o, N, hN,
    hHigh, hEarlier, hk⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  have hdegrees : Nat.card o.orbit = 3 ∨ Nat.card o.orbit = 4 ∨
      Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 9 ∨
      Nat.card o.orbit = 12 ∨ Nat.card o.orbit = 27 :=
    ternaryHigh_action_degree_menu
      hChief hWeight hPrimitive h18 N hHigh
  obtain ⟨d, hd⟩ := C3HighWidthLabel.exists_of_degree_menu hdegrees
  have hdegree : b + 3 = n := by
    have hcard := Nat.card_congr e
    have hternary : Nat.card TernaryCyclic = 3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,
        Nat.card_fin]
    rw [Nat.card_sum, hternary, Nat.card_fin, Nat.card_fin] at hcard
    omega
  subst n
  let C : C3HighNestedCarrier.Data H := ⟨o, N, hN, hHigh⟩
  have hordinary' : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rw [hphysical]
    exact hG.1
  have howner' : FirstOwned (c3PatternStructuralBranchMenu (b + 3)) owner
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  have hnon2 : ¬ IsPGroup 2 A := by
    exact strict_ternaryRelativeHead_not_isPGroup_two N hHigh
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    (C3ComplementSource b H) o hd.symm hnon2
  have haligned : C3HighAlignedOwnerAction
      (c3PhysicalOwnerKindEquiv owner) i.representative :=
    C.alignedOwnerAction_of_chart H hd.symm hEarlier
      (c3PhysicalOwnerKindEquiv owner) hk i.representative eO himage
  let j0 : C3HighFirstOwnerIndex := ⟨d, owner, i⟩
  let j : C3HighAlignedFirstOwnerIndex := ⟨j0, by
    simpa only [j0, c3HighFirstOwnerAction] using haligned⟩
  have hexcluded : ¬ C3HighAlignedDegreeThreeTernary j := by
    rintro ⟨hwidth, hkind⟩
    have hwidth' : d.width = 3 := hwidth
    have horbit : Nat.card C.orbit.orbit = 3 := by
      change Nat.card o.orbit = 3
      rw [← hd]
      exact hwidth'
    have hkind' : c3PhysicalOwnerKindEquiv owner =
        C3PhysicalOwnerKind.ternaryPGroup := hkind
    have hP : IsPGroup 3 A := by
      have h := hk
      rw [hkind'] at h
      exact h
    have hpattern : C1DegreeNineSourcePattern
        (C3HighNestedCarrier.physicalSubgroup H) := by
      apply (c1DegreeNineSourcePattern_relabel_iff e _).mp
      rw [hphysical]
      exact hG.2.2
    exact C.not_degreeThree_ternaryPGroup_of_pattern H horbit hfull hpattern hP
  have hmem := C.mem_non2FirstOwnerCanonicalFamily_forAction
    c3PatternStructuralBranchMenu c3PatternStructuralBranchMenu_natural
      H hd.symm e hordinary' owner howner' i eO himage
  refine ⟨⟨j, hexcluded⟩, ?_⟩
  simpa only [j, j0, c3HighAlignedFirstOwnerAction,
    c3HighAlignedFirstOwnerWidth, c3HighAlignedFirstOwnerPredicate,
    c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
    c3HighFirstOwnerPredicate, hphysical] using hmem

/-- Pointwise estimates for the refined cells assemble at the literal
deleted complement degree. -/
theorem c3PhysicalStructuralOwnerRatio_le_refinedForwardRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighRefinedAlignedIndex → ℕ → ℝ)
    (hlocal : ∀ (j : C3HighRefinedAlignedIndex) (n : ℕ)
      (hn : c3HighAlignedFirstOwnerWidth j.1 ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j.1) hn
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighAlignedFirstOwnerWidth j.1) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j.1))
    (n : ℕ) (hn : 27 ≤ n) :
    c3PhysicalStructuralOwnerRatio n ≤
      ∑ b ∈ Finset.range n,
        fusionForwardRow c3HighRefinedWidth f n b *
          ordinarySubgroupRatio b := by
  let widthLe : ∀ j : C3HighRefinedAlignedIndex,
      c3HighRefinedWidth j ≤ n :=
    fun j => c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le n hn j.1
  have hcard := fusionPhysicalUnion_card_le
    (C3PhysicalStructuralOwnerSet n)
    (fun j : C3HighRefinedAlignedIndex =>
      FusionWidthCanonicalFamily (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1)))
    (c3PhysicalStructuralOwner_refinedAlignedCover
      hChief hWeight hPrimitive h18 n hn)
  have hcardR : (Nat.card (C3PhysicalStructuralOwnerSet n) : ℝ) ≤
      ∑ j : C3HighRefinedAlignedIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
          (c3HighAlignedFirstOwnerPredicate j.1
            (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) := by
    exact_mod_cast hcard
  have hsum :
      ∑ j : C3HighRefinedAlignedIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
            (c3HighAlignedFirstOwnerPredicate j.1
              (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
            exactBenchmark n ≤
        ∑ j : C3HighRefinedAlignedIndex,
          f j (n - c3HighRefinedWidth j) *
            ordinarySubgroupRatio (n - c3HighRefinedWidth j) := by
    apply Finset.sum_le_sum
    intro j _
    exact hlocal j n (widthLe j)
  have hrow := fusionForwardRow_weighted_sum
    c3HighRefinedWidth f c3HighRefinedWidth_pos
    ordinarySubgroupRatio n widthLe
  calc
    c3PhysicalStructuralOwnerRatio n ≤
        (∑ j : C3HighRefinedAlignedIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
            (c3HighAlignedFirstOwnerPredicate j.1
              (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ)) /
          exactBenchmark n :=
      div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ j : C3HighRefinedAlignedIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
          (c3HighAlignedFirstOwnerPredicate j.1
            (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
          exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ j : C3HighRefinedAlignedIndex,
        f j (n - c3HighRefinedWidth j) *
          ordinarySubgroupRatio (n - c3HighRefinedWidth j) := hsum
    _ = _ := hrow.symm

/-- Exponentially decaying estimates on the refined cells give the complete
high-C3 structural-owner continuation. -/
noncomputable def c3PhysicalStructuralOwner_refinedExponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighRefinedAlignedIndex → ℕ → ℝ)
    (hf : ∀ j b, 0 ≤ f j b)
    (hdecay : ∀ j, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ b : ℕ in atTop, f j b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ)))
    (hlocal : ∀ (j : C3HighRefinedAlignedIndex) (n : ℕ)
      (hn : c3HighAlignedFirstOwnerWidth j.1 ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j.1) hn
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighAlignedFirstOwnerWidth j.1) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j.1)) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio := by
  let W := fusionForwardRow_decay c3HighRefinedWidth f
    c3HighRefinedWidth_pos hdecay
  let C : ℝ := Classical.choose W
  have hCκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hCκ
  have hspec := Classical.choose_spec hCκ
  let V := eventually_atTop.mp hspec.2.2
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := fusionForwardRow c3HighRefinedWidth f
      threshold := max 27 N
      rate := κ
      scalarConst := 1
      rowConst := C
      rate_pos := hspec.2.1
      scalarConst_pos := by norm_num
      rowConst_nonneg := hspec.1.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact fusionForwardRow_nonneg c3HighRefinedWidth f hf n b
  · intro n hn
    have hn27 : 27 ≤ n := (le_max_left 27 N).trans hn
    exact (c3PhysicalStructuralOwnerRatio_le_refinedForwardRow
      hChief hWeight hPrimitive h18 f hlocal n hn27).trans_eq
        (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 27 N).trans hn)

end SymmetricSubgroupAsymptotics

end
