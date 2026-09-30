import SymmetricSubgroupAsymptotics.C3PhysicalOwnerFiniteFusion
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra
import SymmetricSubgroupAsymptotics.C1DegreeNineSourcePatternRelabel

/-!
# Finite continuation for the high-C3 physical owners

This is the numerical attachment point for the first c=1 audit.  The six
possible retained widths, their actual non-2 action classes, and the four
first-owner branches form one finite index.  Any exponentially decaying
bound for each resulting canonical physical family therefore gives a single
complete forward estimate for the high-C3 owner sector.

The sector is the split c=1 owner of the manuscript: the complete physical
subgroup has exactly one regular `C3` orbit and no natural `A4` orbit.  This
source pattern is carried by every cell predicate as a conjunct of the
first-owner menu.  The unrestricted branch menu, and therefore the final
residual row, are unchanged.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The high-C3 branch menu evaluated only on complete physical subgroups
with the exact c=1 source pattern. -/
def c3PatternStructuralBranchMenu
    (n : ℕ) (i : Fin 4) (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  c3PhysicalStructuralBranchMenu n i G ∧ C1DegreeNineSourcePattern G

theorem c3PatternStructuralBranchMenu_natural :
    DegreeNaturalOwnerMenu c3PatternStructuralBranchMenu := by
  intro m n hmn e i G
  exact and_congr (c3PhysicalStructuralBranchMenu_natural hmn e i G)
    (c1DegreeNineSourcePattern_relabel_iff e G)

/-- The pattern does not depend on the branch, so it commutes with first
ownership. -/
theorem firstOwned_c3PatternStructuralBranchMenu_iff
    {n : ℕ} (i : Fin 4) (G : Subgroup (Equiv.Perm (Fin n))) :
    FirstOwned (c3PatternStructuralBranchMenu n) i G ↔
      FirstOwned (c3PhysicalStructuralBranchMenu n) i G ∧
        C1DegreeNineSourcePattern G := by
  constructor
  · rintro ⟨⟨hi, hpattern⟩, hprev⟩
    exact ⟨⟨hi, fun j hj hp => hprev j hj ⟨hp, hpattern⟩⟩, hpattern⟩
  · rintro ⟨⟨hi, hprev⟩, hpattern⟩
    exact ⟨⟨hi, hpattern⟩, fun j hj hp => hprev j hj hp.1⟩

abbrev C3HighFirstOwnerIndex :=
  Σ d : C3HighWidthLabel,
    Fin 4 × Non2TransitiveActionClass (Fin d.width)

def c3HighFirstOwnerWidth (j : C3HighFirstOwnerIndex) : ℕ :=
  j.1.width

def c3HighFirstOwnerAction (j : C3HighFirstOwnerIndex) :
    Subgroup (Equiv.Perm (Fin (c3HighFirstOwnerWidth j))) :=
  j.2.2.representative

def c3HighFirstOwnerPredicate (j : C3HighFirstOwnerIndex) (b : ℕ) :
    Subgroup (c3HighFirstOwnerAction j × Equiv.Perm (Fin b)) → Prop :=
  non2FirstOwnerPredicate c3PatternStructuralBranchMenu
    (c3HighFirstOwnerWidth j) (j.2.1, j.2.2) b

theorem c3HighFirstOwnerWidth_pos (j : C3HighFirstOwnerIndex) :
    0 < c3HighFirstOwnerWidth j :=
  C3HighWidthLabel.width_pos j.1

theorem c3HighFirstOwnerWidth_le_of_twentySeven_le
    (n : ℕ) (hn : 27 ≤ n) (j : C3HighFirstOwnerIndex) :
    c3HighFirstOwnerWidth j ≤ n := by
  rcases j with ⟨d, owner, i⟩
  cases d <;> simp only [c3HighFirstOwnerWidth, C3HighWidthLabel.width] <;> omega

theorem c3HighFirstOwnerPredicate_natural
    (j : C3HighFirstOwnerIndex) (b : ℕ) :
    FusionOrbitNatural (c3HighFirstOwnerAction j)
      (c3HighFirstOwnerPredicate j b) := by
  apply non2FirstOwnerPredicate_natural
  intro n owner e G
  exact c3PatternStructuralBranchMenu_natural rfl e owner G

/-- Complete noncritical physical subgroups accepted by the high-C3 owner,
with the exact one-regular-`C3`, no-natural-`A4` c=1 source pattern. -/
def C3PhysicalStructuralOwnerSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {G | ¬ IsCriticalSubgroup n G ∧ C3PhysicalStructuralOwner n G ∧
    C1DegreeNineSourcePattern G}

def c3PhysicalStructuralOwnerRatio (n : ℕ) : ℝ :=
  (Nat.card (C3PhysicalStructuralOwnerSet n) : ℝ) / exactBenchmark n

/-- A first owner of the pattern menu enters the finite canonical family of
the same menu.  The branch data are taken from the unrestricted branch, and
the retained pattern is carried unchanged by the local predicate. -/
theorem c3PatternStructuralBranch_firstOwner_mem_finiteNon2CanonicalFamily
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hordinary : ¬ IsCriticalSubgroup n G)
    (owner : Fin 4)
    (howner : FirstOwned (c3PatternStructuralBranchMenu n) owner G) :
    ∃ (d : C3HighWidthLabel) (hn : d.width ≤ n)
      (i : Non2TransitiveActionClass (Fin d.width)),
      G ∈ FusionWidthCanonicalFamily
        (non2FirstOwnerAction d.width (owner, i)) hn
        (non2FirstOwnerPredicate c3PatternStructuralBranchMenu
          d.width (owner, i) (n - d.width)) := by
  rcases howner.1.1 with ⟨b, e, H, hphysical, _, o, N, hN,
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
    rwa [hphysical]
  have howner' : FirstOwned (c3PatternStructuralBranchMenu (b + 3)) owner
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  obtain ⟨hn, i, hmem⟩ := C.mem_non2FirstOwnerCanonicalFamily_atWidth
    c3PatternStructuralBranchMenu c3PatternStructuralBranchMenu_natural
      H hd.symm e hordinary' owner howner'
  exact ⟨d, hn, i, by simpa only [hphysical] using hmem⟩

/-- The finite first-owner/action families cover the complete high-C3 owner
set.  Each subgroup is assigned to its first branch before its retained orbit
is deleted. -/
theorem c3PhysicalStructuralOwner_finiteFusionCover
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 27 ≤ n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : G ∈ C3PhysicalStructuralOwnerSet n) :
    ∃ j : C3HighFirstOwnerIndex,
      G ∈ FusionWidthCanonicalFamily
        (c3HighFirstOwnerAction j)
        (c3HighFirstOwnerWidth_le_of_twentySeven_le n hn j)
        (c3HighFirstOwnerPredicate j (n - c3HighFirstOwnerWidth j)) := by
  obtain ⟨ownerEligible, hEligible⟩ :=
    c3PhysicalStructuralBranchMenu_cover
      hChief hWeight hPrimitive h18 hG.2.1
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (c3PatternStructuralBranchMenu n) G
      ⟨ownerEligible, hEligible, hG.2.2⟩
  obtain ⟨d, hd, i, hmem⟩ :=
    c3PatternStructuralBranch_firstOwner_mem_finiteNon2CanonicalFamily
      hChief hWeight hPrimitive h18 hG.1 owner howner
  let j : C3HighFirstOwnerIndex := ⟨d, owner, i⟩
  refine ⟨j, ?_⟩
  simpa only [j, c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
    c3HighFirstOwnerPredicate] using hmem

/-- A pointwise bound for every finite owner/action cell assembles into one
forward recurrence at the literal deleted complement degree. -/
theorem c3PhysicalStructuralOwnerRatio_le_forwardRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighFirstOwnerIndex → ℕ → ℝ)
    (hlocal : ∀ (j : C3HighFirstOwnerIndex) (n : ℕ)
      (hn : c3HighFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighFirstOwnerAction j) hn
        (c3HighFirstOwnerPredicate j (n - c3HighFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighFirstOwnerWidth j))
    (n : ℕ) (hn : 27 ≤ n) :
    c3PhysicalStructuralOwnerRatio n ≤
      ∑ b ∈ Finset.range n,
        fusionForwardRow c3HighFirstOwnerWidth f n b *
          ordinarySubgroupRatio b := by
  let widthLe : ∀ j : C3HighFirstOwnerIndex,
      c3HighFirstOwnerWidth j ≤ n :=
    c3HighFirstOwnerWidth_le_of_twentySeven_le n hn
  have hcard := fusionPhysicalUnion_card_le
    (C3PhysicalStructuralOwnerSet n)
    (fun j : C3HighFirstOwnerIndex =>
      FusionWidthCanonicalFamily (c3HighFirstOwnerAction j) (widthLe j)
        (c3HighFirstOwnerPredicate j (n - c3HighFirstOwnerWidth j)))
    (c3PhysicalStructuralOwner_finiteFusionCover
      hChief hWeight hPrimitive h18 n hn)
  have hcardR : (Nat.card (C3PhysicalStructuralOwnerSet n) : ℝ) ≤
      ∑ j : C3HighFirstOwnerIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighFirstOwnerAction j) (widthLe j)
          (c3HighFirstOwnerPredicate j
            (n - c3HighFirstOwnerWidth j))) : ℝ) := by
    exact_mod_cast hcard
  have hsum :
      ∑ j : C3HighFirstOwnerIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighFirstOwnerAction j) (widthLe j)
            (c3HighFirstOwnerPredicate j
              (n - c3HighFirstOwnerWidth j))) : ℝ) /
            exactBenchmark n ≤
        ∑ j : C3HighFirstOwnerIndex,
          f j (n - c3HighFirstOwnerWidth j) *
            ordinarySubgroupRatio (n - c3HighFirstOwnerWidth j) := by
    apply Finset.sum_le_sum
    intro j _
    exact hlocal j n (widthLe j)
  have hrow := fusionForwardRow_weighted_sum
    c3HighFirstOwnerWidth f c3HighFirstOwnerWidth_pos
    ordinarySubgroupRatio n widthLe
  calc
    c3PhysicalStructuralOwnerRatio n ≤
        (∑ j : C3HighFirstOwnerIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighFirstOwnerAction j) (widthLe j)
            (c3HighFirstOwnerPredicate j
              (n - c3HighFirstOwnerWidth j))) : ℝ)) /
          exactBenchmark n :=
      div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ j : C3HighFirstOwnerIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighFirstOwnerAction j) (widthLe j)
          (c3HighFirstOwnerPredicate j
            (n - c3HighFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ j : C3HighFirstOwnerIndex,
        f j (n - c3HighFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighFirstOwnerWidth j) := hsum
    _ = _ := hrow.symm

/-- Exponentially decaying local owner rows give a complete forward-estimate
object for the high-C3 structural owner sector. -/
noncomputable def c3PhysicalStructuralOwner_exponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighFirstOwnerIndex → ℕ → ℝ)
    (hf : ∀ j b, 0 ≤ f j b)
    (hdecay : ∀ j, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ b : ℕ in atTop, f j b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ)))
    (hlocal : ∀ (j : C3HighFirstOwnerIndex) (n : ℕ)
      (hn : c3HighFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighFirstOwnerAction j) hn
        (c3HighFirstOwnerPredicate j (n - c3HighFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighFirstOwnerWidth j)) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio := by
  let W := fusionForwardRow_decay c3HighFirstOwnerWidth f
    c3HighFirstOwnerWidth_pos hdecay
  let C : ℝ := Classical.choose W
  have hCκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hCκ
  have hspec := Classical.choose_spec hCκ
  let V := eventually_atTop.mp hspec.2.2
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := fusionForwardRow c3HighFirstOwnerWidth f
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
    exact fusionForwardRow_nonneg c3HighFirstOwnerWidth f hf n b
  · intro n hn
    have hn27 : 27 ≤ n := (le_max_left 27 N).trans hn
    exact (c3PhysicalStructuralOwnerRatio_le_forwardRow
      hChief hWeight hPrimitive h18 f hlocal n hn27).trans_eq
        (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 27 N).trans hn)

end SymmetricSubgroupAsymptotics

end
