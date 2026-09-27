import SymmetricSubgroupAsymptotics.BinaryPairZeroCutPositiveFusion
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterDirectFusion

/-!
# The original binary orbit sectors of degree 1024 and 2048

Their zero cuts have a positive gap, sufficient for a fixed finite direct
row. Each original action class has one chosen pairing and every literal
normal is retained. The physical sector is unmarked, with an unrestricted
complement and its original correlations. No class-count or coarse-growth
input is needed for this zero-cut installation.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryOriginalFinitePrefixPhysical

def pairExponent (t : Fin 2) : ℕ := 9+t.1
def halfWidth (t : Fin 2) : ℕ := 2^(pairExponent t)

theorem pairExponent_ge (t : Fin 2) : 9 ≤ pairExponent t := by
  unfold pairExponent
  omega

theorem halfWidth_pos (t : Fin 2) : 0 < halfWidth t := pow_pos (by decide) _

theorem width_le (t : Fin 2) : 2*halfWidth t ≤ 2048 := by
  have he : pairExponent t ≤ 10 := by
    unfold pairExponent
    have ht := t.2
    omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he
  norm_num only [show (2:ℕ)^10 = 1024 by norm_num] at hp
  change 2*2^(pairExponent t) ≤ 2048
  omega

/-- One actual conjugacy class at each of the two original degrees. -/
abbrev Action := Σ t : Fin 2, BinaryTransitiveActionClass (Fin (2*halfWidth t))

def halfDegree (i : Action) : ℕ := halfWidth i.1
def action (i : Action) : Subgroup (Equiv.Perm (Fin (2*halfDegree i))) :=
  i.2.representative

local instance actionPretransitive (i : Action) :
    MulAction.IsPretransitive (action i) (Fin (2*halfDegree i)) :=
  i.2.representative_pretransitive

/-- This original pairing is fixed independently of every exterior group. -/
def pairing (i : Action) : RealizedPairing (action i) (Fin (halfDegree i)) := by
  apply Classical.choice
  exact transitiveBinaryRealizedPairing_nonempty (pairExponent i.1)
    i.2.representative i.2.representative_isPGroup (by
      rw [Nat.card_fin]
      change 2*2^(pairExponent i.1) = 2^(pairExponent i.1+1)
      rw [pow_succ, Nat.mul_comm])

local instance prefixOriginalNormal (i : Action)
    (N : {N : Subgroup (action i) // N.Normal}) : N.1.Normal := N.2

/-- The actual faithful top-cover degree is the zero-cut marker. -/
def prefixDegree (i : Action) (_N : {N : Subgroup (action i) // N.Normal}) : ℕ := halfDegree i

def markerHalf (i : Action) (_N : {N : Subgroup (action i) // N.Normal}) : ℕ :=
  2^(pairExponent i.1-1)

def liftConstant (i : Action) (N : {N : Subgroup (action i) // N.Normal}) : ℝ :=
  (pairing i).chosenFrame.zeroCutLiftConstant N.1

def gapParameter (i : Action) (N : {N : Subgroup (action i) // N.Normal}) : ℝ :=
  (pairing i).chosenFrame.zeroCutGapParameter N.1

def momentWeight (i : Action) (N : {N : Subgroup (action i) // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  (pairing i).chosenFrame.zeroCutMomentWeight N.1 J

theorem prefix_lt (i : Action) (N : {N : Subgroup (action i) // N.Normal}) :
    prefixDegree i N < 2*halfDegree i := by
  have hp := halfWidth_pos i.1
  change halfWidth i.1 < 2*halfWidth i.1
  omega

theorem prefix_eq_two_mul (i : Action)
    (N : {N : Subgroup (action i) // N.Normal}) :
    prefixDegree i N = 2*markerHalf i N := by
  have hk : 1 ≤ pairExponent i.1 := (show 1 ≤ 9 by decide).trans (pairExponent_ge i.1)
  change 2^(pairExponent i.1) = 2*2^(pairExponent i.1-1)
  rw [Nat.mul_comm 2, ← pow_succ, Nat.sub_add_cancel hk]

theorem liftConstant_nonneg (i : Action)
    (N : {N : Subgroup (action i) // N.Normal}) : 0 ≤ liftConstant i N := by
  unfold liftConstant BinaryPairFrame.zeroCutLiftConstant
  positivity

theorem gapParameter_pos (i : Action)
    (N : {N : Subgroup (action i) // N.Normal}) : 0 < gapParameter i N := by
  have hz := (pairing i).chosenFrame.zeroCut_positive_parameters N.1
    i.2.representative_isPGroup (pairExponent i.1) (pairExponent_ge i.1)
    (show Nat.card (Fin (halfDegree i)) = 2^(pairExponent i.1) from Nat.card_fin _)
  exact hz.2.2.1

theorem moment_le (i : Action) (N : {N : Subgroup (action i) // N.Normal})
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), momentWeight i N J) ≤
      (subgroupCount (b+prefixDegree i N) : ℝ) := by
  simpa only [momentWeight, prefixDegree, Nat.card_fin, pow_one, one_mul] using
    (pairing i).chosenFrame.zeroCutMomentWeight_moment_le N.1 b 1

theorem original_envelope (i : Action)
    (N : {N : Subgroup (action i) // N.Normal}) {b : ℕ}
    (P : Subgroup (action i × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (action i) P N J ≤
      fusionLocalFactor b (halfDegree i) (prefixDegree i N) (liftConstant i N)
        (gapParameter i N)*momentWeight i N J := by
  simpa only [prefixDegree, liftConstant, gapParameter, momentWeight, Nat.card_fin] using
    (pairing i).chosenFrame.zeroCut_original_survivingEpiCount_le N.1 P J

/-- Original subgroups with a binary orbit of one of the two degrees.
Neither the whole subgroup nor its complement is required to be binary. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ t : Fin 2, ∃ x : Fin n,
    Nat.card (MulAction.orbit H x) = 2*halfWidth t ∧
      IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x)}

theorem cover {n : ℕ} (hn : 2048 ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H ∈ physicalFamily n) :
    ∃ i : Action, H ∈ FusionCanonicalFamily (action i)
      ((width_le i.1).trans hn) (fun _ => True) := by
  obtain ⟨t,x,hw,hP⟩ := hH
  obtain ⟨i,hi⟩ := FusionOrbitRepresentativeCharts.exists_canonicalFamily H x hw hP
    ((width_le t).trans hn)
  exact ⟨⟨t,i⟩,hi⟩

/-- The exact original representative/normal row. Its two target degrees
are n-512 and n-1024 whenever the corresponding orbit fits. -/
def directRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow halfDegree action prefixDegree liftConstant gapParameter n m

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  fusionPhysicalDirectRow_nonneg halfDegree action prefixDegree liftConstant gapParameter
    liftConstant_nonneg n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m = 0 :=
  fusionPhysicalDirectRow_forward halfDegree action prefixDegree liftConstant gapParameter
    prefix_lt hnm

/-- The finite family supplies all actual envelopes and first moments;
there is no external cover, capacity, class-count or coarse-growth premise. -/
theorem direct_recurrence (n : ℕ) (hn : 2048 ≤ n) :
    (Nat.card (physicalFamily n) : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) :=
  fusionPhysicalUnion_direct_recurrence halfDegree action n
    (fun i => (width_le i.1).trans hn) (physicalFamily n) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (cover hn)
    prefixDegree liftConstant gapParameter (fun i N J => momentWeight i N J)
    prefix_lt liftConstant_nonneg
    (fun i N J => original_envelope i N (fun _ => True) J)
    (fun i N => moment_le i N (n-2*halfDegree i))

/-- Exponential aggregate decay is proved for the complete finite row,
before any bound is assumed on the unknown ordinary subgroup sequence. -/
theorem directRow_decay :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, directRow n m) ≤ C*(2:ℝ)^(-κ*(n:ℝ)) :=
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
    ∀ᶠ n : ℕ in atTop, (∑ m ∈ Finset.range n, directRow n m) ≤ 1/2 :=
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

/-- Any additional ownership exclusions use a literal subtype inclusion. -/
theorem filtered_direct_recurrence (n : ℕ) (hn : 2048 ≤ n)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // P H.1} : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // P H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

end SymmetricSubgroupAsymptotics.BinaryOriginalFinitePrefixPhysical

end
