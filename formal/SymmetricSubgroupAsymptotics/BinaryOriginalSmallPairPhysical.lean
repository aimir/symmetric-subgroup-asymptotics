import SymmetricSubgroupAsymptotics.BinaryPairSmallSectionCut
import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.OriginalCentralCutFusion
import SymmetricSubgroupAsymptotics.BinaryPermutationClassBound
import SymmetricSubgroupAsymptotics.BinaryOrderSevenCharacterFusion
import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterDirectFusion

/-! Actual original binary orbit sectors of degrees32 through512.
Each original action class has one pairing fixed before the exterior is
chosen. Every literal original normal uses either the proved small-section
central cut or the proved large-section character entry. All lift constants,
quotients and normalizer weights remain original. The exterior is arbitrary.
No class-count, capacity, coarse-growth or physical-cover premise remains.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryOriginalSmallPairPhysical

def pairExponent (t : Fin 5) : ℕ := 4+t.1
def halfWidth (t : Fin 5) : ℕ := 2^(pairExponent t)

theorem pairExponent_ge (t : Fin 5) : 4≤pairExponent t := by
  unfold pairExponent
  omega

theorem halfWidth_pos (t : Fin 5) : 0<halfWidth t := pow_pos (by decide) _

theorem halfWidth_even (t : Fin 5) : halfWidth t=2*2^(pairExponent t-1) := by
  have hk : 1≤pairExponent t := (by decide : 1≤4).trans (pairExponent_ge t)
  unfold halfWidth
  rw [Nat.mul_comm 2,← pow_succ,Nat.sub_add_cancel hk]

theorem width_le (t : Fin 5) : 2*halfWidth t≤512 := by
  have he : pairExponent t≤8 := by
    unfold pairExponent
    have ht := t.2
    omega
  have hp := Nat.pow_le_pow_right (by decide : 0<2) he
  norm_num only [show (2:ℕ)^8=256 by norm_num] at hp
  change 2*2^(pairExponent t)≤512
  omega

abbrev Action := Σ t : Fin 5, BinaryTransitiveActionClass (Fin (2*halfWidth t))

def halfDegree (i : Action) : ℕ := halfWidth i.1
def action (i : Action) : Subgroup (Equiv.Perm (Fin (2*halfDegree i))) :=
  i.2.representative

local instance actionPretransitive (i : Action) :
    MulAction.IsPretransitive (action i) (Fin (2*halfDegree i)) :=
  i.2.representative_pretransitive

/-- One actual pairing, independent of the normal axis and exterior. -/
def pairing (i : Action) : RealizedPairing (action i) (Fin (halfDegree i)) := by
  apply Classical.choice
  exact transitiveBinaryRealizedPairing_nonempty (pairExponent i.1)
    i.2.representative i.2.representative_isPGroup (by
      rw [Nat.card_fin]
      change 2*2^(pairExponent i.1)=2^(pairExponent i.1+1)
      rw [pow_succ,Nat.mul_comm])

local instance pairTopPretransitive (i : Action) :
    MulAction.IsPretransitive (pairing i).chosenFrame.top.range (Fin (halfDegree i)) :=
  (pairing i).chosenFrame.top_pretransitive

local instance smallPairOriginalNormal (i : Action)
    (N : {N : Subgroup (action i) // N.Normal}) : N.1.Normal := N.2

abbrev sectionModule (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    Rep (ZMod 2) (action i ⧸ ((pairing i).chosenFrame.top.ker⊔N.1)) :=
  Rep.of ((pairing i).chosenFrame.sectionRepresentation N.1)

/-- This internal bundle is constructed below from actual objects for
every axis; none of its counting fields is a premise of the final theorem. -/
structure LocalEntry (i : Action) (N : {N : Subgroup (action i) // N.Normal}) where
  prefixDegree : ℕ
  markerHalf : ℕ
  liftConstant : ℝ
  gapParameter : ℝ
  momentWeight : {b : ℕ} → Subgroup (Equiv.Perm (Fin b)) → ℝ
  prefix_eq_two_mul : prefixDegree=2*markerHalf
  prefix_lt : prefixDegree<2*halfDegree i
  liftConstant_nonneg : 0≤liftConstant
  gapParameter_pos : 0<gapParameter
  moment_le : ∀ b q : ℕ,
    (∑ J : Subgroup (Equiv.Perm (Fin b)),momentWeight J^q)≤
      (subgroupCount (b+q*prefixDegree):ℝ)
  original_envelope : ∀ {b : ℕ}
    (P : Subgroup (action i × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (action i) P N J≤
      fusionLocalFactor b (halfDegree i) prefixDegree liftConstant gapParameter*momentWeight J

/-- Choose one proved central cut in the same actual section. Its
cardinality and H1 belong to that actual quotient representation. -/
def smallEntry (i : Action) (N : {N : Subgroup (action i) // N.Normal})
    (hsmall : 2*Module.finrank (ZMod 2) (sectionModule i N)≤halfDegree i) :
    LocalEntry i N := by
  let F := (pairing i).chosenFrame
  let hex := F.exists_small_section_cut_of_top N.1 i.2.representative_isPGroup
    (pairExponent i.1) (pairExponent_ge i.1) (Nat.card_fin _) hsmall
  let C := Classical.choose hex
  have hexC := Classical.choose_spec hex
  let hC := Classical.choose hexC
  have hcost := Classical.choose_spec hexC
  let cut : {C : Submodule (ZMod 2) (sectionModule i N) //
      C≤(sectionModule i N).ρ.invariants} := ⟨C,hC⟩
  have hcost' : (2:ℝ)*Module.finrank (ZMod 2) cut.1+
      4*OriginalCentralCutFusion.capacity (sectionModule i N) cut+2≤(halfDegree i:ℝ) := by
    change (2:ℝ)*Module.finrank (ZMod 2) C+
      4*representationSchurCapacity (F.cutRepresentation N.1 C hC)+2≤(halfDegree i:ℝ)
    simpa only [halfDegree,halfWidth,Nat.cast_pow,Nat.cast_ofNat] using hcost
  have hstrict : (2:ℝ)*Module.finrank (ZMod 2) cut.1+
      4*OriginalCentralCutFusion.capacity (sectionModule i N) cut<(halfDegree i:ℝ) := by
    linarith
  refine {
    prefixDegree := OriginalCentralCutFusion.prefixDegree (sectionModule i N) cut (halfDegree i)
    markerHalf := 2^(pairExponent i.1-1)+Module.finrank (ZMod 2) cut.1
    liftConstant := OriginalCentralCutFusion.liftConstant (sectionModule i N) cut
    gapParameter := OriginalCentralCutFusion.gapParameter (sectionModule i N) cut
      (2*halfDegree i) (halfDegree i)
    momentWeight := fun {b} J => OriginalCentralCutFusion.momentWeight (sectionModule i N) cut J
    prefix_eq_two_mul := ?_
    prefix_lt := OriginalCentralCutFusion.prefixDegree_lt_of_cost
      (sectionModule i N) cut (halfDegree i) hstrict
    liftConstant_nonneg := OriginalCentralCutFusion.liftConstant_nonneg (sectionModule i N) cut
    gapParameter_pos := OriginalCentralCutFusion.gapParameter_pos_of_cost
      (sectionModule i N) cut (halfDegree i) hstrict
    moment_le := ?_
    original_envelope := ?_ }
  · change halfDegree i + 2*Module.finrank (ZMod 2) cut.1 =
      2*(2^(pairExponent i.1-1)+Module.finrank (ZMod 2) cut.1)
    have heven : halfDegree i = 2*2^(pairExponent i.1-1) := halfWidth_even i.1
    omega
  · intro b q
    exact OriginalCentralCutFusion.momentWeight_moment_le (sectionModule i N) cut
      F.top.range.subtype Subtype.val_injective (F.sectionTopQuotient N.1)
      (F.sectionTopQuotient_surjective N.1) b q
  · intro b P J
    exact OriginalCentralCutFusion.original_survival_localFactor_le (sectionModule i N) cut
      (F.zeroCutBase N.1) (F.zeroCutBase_surjective N.1) (F.sectionModuleChart N.1)
      (halfDegree i) (halfDegree i) J
      (fun f => P (fusionFullGoursatEncode N J f).1)

private theorem class_input : BinarySevenPermutationClassInput := by
  intro b P hP
  simpa only [Nat.card_fin] using
    BinaryPermutationClassBound.literal_class_card_pow_seven_le (Fin b) P hP

/-- The large branch retains the original automorphism factor and uses
the now proved binary class theorem, with no supplied class-bound premise. -/
def largeEntry (i : Action) (N : {N : Subgroup (action i) // N.Normal})
    (hlarge : halfDegree i<2*Module.finrank (ZMod 2) (sectionModule i N)) :
    LocalEntry i N := by
  let F := (pairing i).chosenFrame
  let C : BinarySevenCharacterCriterion (action i ⧸ N.1) (2*halfDegree i) := by
    simpa only [Nat.card_fin] using F.largeSectionSevenCriterion N.1
      i.2.representative_isPGroup (pairExponent i.1) (pairExponent_ge i.1)
      (Nat.card_fin _) hlarge
  let E : BinaryOrderSevenCharacterCertificate (action i) N.1 := .inr C
  exact {
    prefixDegree := E.prefixDegree
    markerHalf := E.markerHalf
    liftConstant := E.liftConstant
    gapParameter := E.gapParameter
    momentWeight := fun {b} J => E.momentWeight J
    prefix_eq_two_mul := E.prefixDegree_eq_two_mul
    prefix_lt := E.prefixDegree_lt (Nat.mul_pos (by decide) (halfWidth_pos i.1))
    liftConstant_nonneg := E.liftConstant_nonneg
    gapParameter_pos := E.gapParameter_pos
    moment_le := E.moment_le
    original_envelope := fun {b} P J => E.original_envelope class_input
      i.2.representative_isPGroup P J }

/-- Complete selection, fixed before the exterior degree or source is
chosen; there are no excluded original normals. -/
def selectedEntry (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    LocalEntry i N :=
  if hs : 2*Module.finrank (ZMod 2) (sectionModule i N)≤halfDegree i
  then smallEntry i N hs else largeEntry i N (Nat.lt_of_not_ge hs)

def prefixDegree (i : Action) (N : {N : Subgroup (action i) // N.Normal}) : ℕ :=
  (selectedEntry i N).prefixDegree
def markerHalf (i : Action) (N : {N : Subgroup (action i) // N.Normal}) : ℕ :=
  (selectedEntry i N).markerHalf
def liftConstant (i : Action) (N : {N : Subgroup (action i) // N.Normal}) : ℝ :=
  (selectedEntry i N).liftConstant
def gapParameter (i : Action) (N : {N : Subgroup (action i) // N.Normal}) : ℝ :=
  (selectedEntry i N).gapParameter
def momentWeight (i : Action) (N : {N : Subgroup (action i) // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  (selectedEntry i N).momentWeight J

theorem prefix_lt (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    prefixDegree i N<2*halfDegree i := (selectedEntry i N).prefix_lt

theorem prefix_eq_two_mul (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    prefixDegree i N=2*markerHalf i N := (selectedEntry i N).prefix_eq_two_mul

theorem liftConstant_nonneg (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    0≤liftConstant i N := (selectedEntry i N).liftConstant_nonneg

theorem gapParameter_pos (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    0<gapParameter i N := (selectedEntry i N).gapParameter_pos

theorem moment_le (i : Action) (N : {N : Subgroup (action i) // N.Normal}) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),momentWeight i N J)≤
      (subgroupCount (b+prefixDegree i N):ℝ) := by
  simpa only [momentWeight,prefixDegree,pow_one,one_mul] using
    (selectedEntry i N).moment_le b 1

theorem original_envelope (i : Action) (N : {N : Subgroup (action i) // N.Normal})
    {b : ℕ} (P : Subgroup (action i × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (action i) P N J≤
      fusionLocalFactor b (halfDegree i) (prefixDegree i N) (liftConstant i N)
        (gapParameter i N)*momentWeight i N J :=
  (selectedEntry i N).original_envelope P J

/-- An unmarked family of original ambient subgroups. Only the selected
orbit image is binary; the whole group and its complement are unrestricted. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ t : Fin 5, ∃ x : Fin n,
    Nat.card (MulAction.orbit H x)=2*halfWidth t ∧
      IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x)}

theorem cover {n : ℕ} (hn : 512≤n)
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H∈physicalFamily n) :
    ∃ i : Action, H∈FusionCanonicalFamily (action i)
      ((width_le i.1).trans hn) (fun _ => True) := by
  obtain ⟨t,x,hw,hP⟩ := hH
  obtain ⟨i,hi⟩ := FusionOrbitRepresentativeCharts.exists_canonicalFamily H x hw hP
    ((width_le t).trans hn)
  exact ⟨⟨t,i⟩,hi⟩

/-- Sum every original representative/normal contribution, preserving
duplicates that happen to reach the same smaller degree. -/
def directRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow halfDegree action prefixDegree liftConstant gapParameter n m

theorem directRow_nonneg (n m : ℕ) : 0≤directRow n m :=
  fusionPhysicalDirectRow_nonneg halfDegree action prefixDegree liftConstant gapParameter
    liftConstant_nonneg n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m=0 :=
  fusionPhysicalDirectRow_forward halfDegree action prefixDegree liftConstant gapParameter
    prefix_lt hnm

/-- The actual original-weight recurrence, with no bound assumed on
the unknown ordinary subgroup-count sequence. -/
theorem direct_recurrence (n : ℕ) (hn : 512≤n) :
    (Nat.card (physicalFamily n):ℝ)/exactBenchmark n≤
      ∑ m∈Finset.range n,directRow n m*((subgroupCount m:ℝ)/exactBenchmark m) :=
  fusionPhysicalUnion_direct_recurrence halfDegree action n
    (fun i => (width_le i.1).trans hn) (physicalFamily n) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (cover hn)
    prefixDegree liftConstant gapParameter (fun i N J => momentWeight i N J)
    prefix_lt liftConstant_nonneg
    (fun i N J => original_envelope i N (fun _ => True) J)
    (fun i N => moment_le i N (n-2*halfDegree i))

theorem directRow_decay :
    ∃ C κ : ℝ,0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m∈Finset.range n,directRow n m)≤C*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis halfDegree action => halfDegree j.1)
    (fun j => prefixDegree j.1 j.2) (fun j => markerHalf j.1 j.2)
    (fun j => liftConstant j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor halfDegree action j.1)
    (fun j => gapParameter j.1 j.2)
    (fun j => prefix_lt j.1 j.2) (fun j => prefix_eq_two_mul j.1 j.2)
    (fun j => liftConstant_nonneg j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos halfDegree action j.1)
    (fun j => gapParameter_pos j.1 j.2)

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop,(∑ m∈Finset.range n,directRow n m)≤1/2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis halfDegree action => halfDegree j.1)
    (fun j => prefixDegree j.1 j.2) (fun j => markerHalf j.1 j.2)
    (fun j => liftConstant j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor halfDegree action j.1)
    (fun j => gapParameter j.1 j.2)
    (fun j => prefix_lt j.1 j.2) (fun j => prefix_eq_two_mul j.1 j.2)
    (fun j => liftConstant_nonneg j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos halfDegree action j.1)
    (fun j => gapParameter_pos j.1 j.2)

/-- Ownership exclusions are a literal inclusion of original subgroups,
so no naturality premise for the additional predicate is required. -/
theorem filtered_direct_recurrence (n : ℕ) (hn : 512≤n)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // P H.1}:ℝ)/exactBenchmark n≤
      ∑ m∈Finset.range n,directRow n m*((subgroupCount m:ℝ)/exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // P H.1}≤Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

end SymmetricSubgroupAsymptotics.BinaryOriginalSmallPairPhysical
