import SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCubeStrings
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute

/-! Actual outer-simple conjugation on the eight middle roots. A zero
bit is raised with one fixed integral UNIT sign, valid in every ring;
a one bit commutes. No characteristic-dependent Chevalley coefficient
or tensor-coordinate normalization is supplied as an assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdges
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGTrialityD4NormTwo
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4MiddleCube CFSGTrialityD4MiddleCubeStrings
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckSectionRootLabels
open CFSGTrialityFixedWeylWords CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSignedRootCollecting
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateRaisedRoot
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

abbrev UnitsD4 (K : Type) [CommRing K] := (Matrix GeckIndex GeckIndex K)ˣ

def outerWord (K : Type) [CommRing K] (j : Fin 3) (t : K) : UnitsD4 K :=
  canonicalRoot rawData K false (outerNode j) t

def cubeWord (K : Type) [CommRing K] (a : Cube) (t : K) : UnitsD4 K :=
  selectedRootElement A hd hs hp ho K (cubeRoot a) t

private theorem conjugate_of_commutator {G : Type*} [Group G] (x y z : G)
    (h : x*y*x⁻¹*y⁻¹=z) : x*y*x⁻¹=z*y := by
  calc
    _ = (x*y*x⁻¹*y⁻¹)*y := by group
    _ = z*y := congrArg (fun w => w*y) h

theorem zero_bit_conjugation_sign (a : Cube) (j : Fin 3) (hbit : a j = 0) :
    ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧ ∀ (K : Type) [CommRing K] (t b : K),
      outerWord K j t * cubeWord K a b * (outerWord K j t)⁻¹ =
        cubeWord K (Function.update a j 1) ((ε:K)*(b*t)) * cubeWord K a b := by
  have hpair : integerPairing A (cubeRoot a).val (Index (outerNode j) : Roots A).val = -1 := by
    rw [← short_seed_index, cube_outer_pairing, hbit]
    norm_num
  have hroot : raisedRoot A hd hs hp ho (cubeRoot a) (outerNode j) hpair =
      cubeRoot (Function.update a j 1) := by
    apply Subtype.ext
    change (cubeRoot a).val + (Index (outerNode j) : Roots A).val =
      (cubeRoot (Function.update a j 1)).val
    rw [← short_seed_index, cube_update_val a j hbit]
  obtain ⟨ε, hε, hcollect⟩ := simple_positive_commutator_sign A hd hs hp ho
    (cubeRoot a) (cubeRoot_positive a) (outerNode j) hpair
  refine ⟨ε, hε, ?_⟩
  intro K _ t b
  have h := hcollect K t b
  rw [hroot] at h
  change outerWord K j t * cubeWord K a b * (outerWord K j t)⁻¹ *
    (cubeWord K a b)⁻¹ = cubeWord K (Function.update a j 1) ((ε:K)*(b*t)) at h
  exact conjugate_of_commutator _ _ _ h

theorem one_bit_commutes (K : Type) [CommRing K] (a : Cube) (j : Fin 3)
    (hbit : a j = 1) (t b : K) : Commute (outerWord K j t) (cubeWord K a b) := by
  obtain ⟨ε, hε, hparam⟩ := selected_simple_root_sign A hd hs hp ho (outerNode j)
  have hεsq : (ε:K)*(ε:K)=1 := by rcases hε with rfl | rfl <;> norm_num
  have houter : selectedRootElement A hd hs hp ho K (Index (outerNode j)) ((ε:K)*t) =
      outerWord K j t := by
    have h := hparam K ((ε:K)*t)
    change selectedRootElement A hd hs hp ho K (Index (outerNode j)) ((ε:K)*t) =
      outerWord K j ((ε:K)*((ε:K)*t)) at h
    rw [← mul_assoc, hεsq, one_mul] at h
    exact h
  have hpositive : ∀ i, 0 ≤ (Index (outerNode j) : Roots A).val i := by
    rw [← short_seed_index]
    exact short_positive 0 j
  have hpair : integerPairing A (Index (outerNode j) : Roots A).val (cubeRoot a).val = 1 := by
    rw [integer_symmetric A hs, ← short_seed_index, cube_outer_pairing, hbit]
    norm_num
  rw [← houter]
  exact CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute A hd hs hp ho K
    (Index (outerNode j)) (cubeRoot a) hpositive (cubeRoot_positive a) (Or.inr hpair) _ b

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdges
