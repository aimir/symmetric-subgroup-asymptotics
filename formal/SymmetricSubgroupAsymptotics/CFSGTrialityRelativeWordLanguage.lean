import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatCell
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
import SymmetricSubgroupAsymptotics.CFSGTrialityD4WordDiscriminant

/-! Words in the two literal triality-fixed Weyl words. Every expanded
word is actually fixed on the original natural matrices, hence its
actual root action commutes with triality by proved block uniqueness.
The six signed long roots are reached by displayed relative words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4InvariantRoots CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4WordDiscriminant CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckFixedBruhatCell CFSGTrialityGeckWeylBlocks
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

def expandRelative : List Bool → List (Fin 4)
  | [] => []
  | false :: w => [0,2,3] ++ expandRelative w
  | true :: w => [1] ++ expandRelative w

theorem expandRelative_append (u v : List Bool) :
    expandRelative (u ++ v) = expandRelative u ++ expandRelative v := by
  induction u with
  | nil => rfl
  | cons i u ih => cases i <;> simp only [List.cons_append, expandRelative, ih, List.append_assoc]

private theorem canonicalWord_append (K : Type) [CommRing K] (u v : List (Fin 4)) :
    canonicalWord rawData K (u ++ v) = canonicalWord rawData K u * canonicalWord rawData K v := by
  induction u with
  | nil => simp only [List.nil_append, canonicalWord, one_mul]
  | cons i u ih => rw [List.cons_append, canonicalWord, ih, canonicalWord, mul_assoc]

theorem relative_word_fixed (K : Type) [CommRing K] (σ : K ≃+* K) (w : List Bool) :
    unitTwist K σ (canonicalWord rawData K (expandRelative w)) =
      canonicalWord rawData K (expandRelative w) := by
  induction w with
  | nil => simp only [expandRelative, canonicalWord, map_one]
  | cons i w ih =>
    cases i
    · change unitTwist K σ (canonicalWord rawData K ([0,2,3] ++ expandRelative w)) =
        canonicalWord rawData K ([0,2,3] ++ expandRelative w)
      simp only [canonicalWord_append, map_mul, ih]
      change unitTwist K σ (shortWeyl K) * canonicalWord rawData K (expandRelative w) =
        shortWeyl K * canonicalWord rawData K (expandRelative w)
      rw [shortWeyl_fixed]
    · change unitTwist K σ (canonicalWord rawData K ([1] ++ expandRelative w)) =
        canonicalWord rawData K ([1] ++ expandRelative w)
      simp only [canonicalWord_append, map_mul, ih]
      change unitTwist K σ (longWeyl K) * canonicalWord rawData K (expandRelative w) =
        longWeyl K * canonicalWord rawData K (expandRelative w)
      rw [longWeyl_fixed]

theorem relative_root_action_commutes (w : List Bool) (k : Roots (CartanMatrix.D 4)) :
    diagramRoot (rootAction (expandRelative w) k) = rootAction (expandRelative w) (diagramRoot k) := by
  let B := borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index ℚ
  have hf : unitTwist ℚ (RingEquiv.refl ℚ)
      (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index ℚ (expandRelative w)) =
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index ℚ (expandRelative w) := by
    simpa only [word_eq_canonicalWord] using relative_word_fixed ℚ (RingEquiv.refl ℚ) w
  have hi := fixed_bruhat_cell_block ℚ (RingEquiv.refl ℚ)
    (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index ℚ (expandRelative w)) 1 1 (expandRelative w)
      hf B.one_mem B.one_mem (by simp only [one_mul, mul_one])
  exact block_invariance_root_commutes (expandRelative w) hi k

def relativeLongWord (s : Fin 3) : List Bool := ![[], [false], [true,false]] s

theorem expand_relativeLongWord (s : Fin 3) : expandRelative (relativeLongWord s) = longWord s := by
  fin_cases s <;> rfl

theorem relativeLongWord_root (s : Fin 3) :
    rootAction (expandRelative (relativeLongWord s)) (Index 1) = longRoot s := by
  rw [expand_relativeLongWord]
  exact (congrArg (rootAction (longWord s)) long_seed_index).symm.trans (long_word_label s)

theorem rootAction_negative (w : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    rootAction w (negativeRoot k) = negativeRoot (rootAction w k) := by
  apply Subtype.ext
  rw [wordRoot_negative_val, negative_val]

def relativeSignedLongWord (neg : Bool) (s : Fin 3) : List Bool :=
  if neg then relativeLongWord s ++ [true] else relativeLongWord s

theorem relativeSignedLongWord_root (neg : Bool) (s : Fin 3) :
    rootAction (expandRelative (relativeSignedLongWord neg s)) (Index 1) = signedLongRoot neg s := by
  cases neg
  · exact relativeLongWord_root s
  · change rootAction (expandRelative (relativeLongWord s ++ [true])) (Index 1) =
      negativeRoot (longRoot s)
    rw [expandRelative_append]
    change rootAction (expandRelative (relativeLongWord s) ++ [1]) (Index 1) = _
    dsimp only [rootAction]
    rw [wordRoot_append]
    change rootAction (expandRelative (relativeLongWord s)) (negativeRoot (Index 1)) = _
    rw [rootAction_negative, relativeLongWord_root]

theorem central_stabilizer_expand :
    expandRelative [false,true,false,true,false] = [0,2,3,1,0,2,3,1,0,2,3] := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage
