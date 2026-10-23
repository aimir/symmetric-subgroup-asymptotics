import SymmetricSubgroupAsymptotics.CFSGTrialityD4InvariantRoots
import SymmetricSubgroupAsymptotics.CFSGTrialityD4FixedWeylPilot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords

/-! Literal Weyl words satisfy the two mod-two invariants in their
actual integral linear action. When that root action commutes with
triality, its first column satisfies the selected stabilizer pilot's
explicit discriminant conditions; no such condition is a new input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4WordDiscriminant
open CFSGTrialityD4NormTwo CFSGTrialityD4InvariantRoots CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4FixedWeylPilot CFSGD4WeylDiscriminant CFSGIntegerMatrixColumnTransport
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGNormTwoCartanDiagramWords CFSGSerreDiagram

abbrev rootAction (w : List (Fin 4)) := wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
  D4_positive_definite Base Index w

abbrev linearAction (w : List (Fin 4)) := wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
  D4_positive_definite Base Index w

theorem wordLinear_discriminant (w : List (Fin 4)) (c : Fin 2) :
    integerVector (ZMod 2) (linearAction w (discriminantLift c)) = discriminantResidue c := by
  have he := LinearMap.congr_fun (latticeWord_linear (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) w)
    (discriminantLift c)
  change latticeWord (CartanMatrix.D 4) w *ᵥ discriminantLift c =
    linearAction w (discriminantLift c) at he
  have hc : integerVector (ZMod 2) (discriminantLift c) = discriminantResidue c := by
    fin_cases c <;> decide
  calc
    _ = integerVector (ZMod 2) (latticeWord (CartanMatrix.D 4) w *ᵥ discriminantLift c) :=
      congrArg (integerVector (ZMod 2)) he.symm
    _ = (Int.castRingHom (ZMod 2)).mapMatrix (latticeWord (CartanMatrix.D 4) w) *ᵥ
        integerVector (ZMod 2) (discriminantLift c) :=
      (map_mulVec (ZMod 2) _ _).symm
    _ = discriminantResidue c := by rw [hc]; exact word_fixes w c

theorem diagramRoot_cycle (k : Roots (CartanMatrix.D 4)) :
    (diagramRoot k).val = cycleCoordinates k.val := by
  funext i
  change k.val (trialityPermutation.symm i) = k.val (![3,1,0,2] i)
  rw [triality_symm_apply]

theorem diagramRoot_index (i : Fin 4) :
    diagramRoot (Index i : Roots (CartanMatrix.D 4)) =
      (Index (trialityPermutation i) : Roots (CartanMatrix.D 4)) :=
  simple_rootPermutation (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) trialityPermutation triality_preserves i

theorem word_column_triality (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) (i : Fin 4) :
    linearAction w (Pi.single (trialityPermutation i) (1 : ℤ) : Fin 4 → ℤ) =
      cycleCoordinates (linearAction w (Pi.single i (1 : ℤ) : Fin 4 → ℤ)) := by
  have he := hcomm (Index i)
  rw [diagramRoot_index] at he
  calc
    _ = (rootAction w (Index (trialityPermutation i))).val :=
      wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w (Index (trialityPermutation i))
    _ = (diagramRoot (rootAction w (Index i))).val := congrArg Subtype.val he.symm
    _ = cycleCoordinates (rootAction w (Index i)).val := diagramRoot_cycle _
    _ = _ := congrArg cycleCoordinates (wordLinear_root (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index w (Index i)).symm

theorem word_outer_discriminants (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    outerDiscriminants (linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ)) := by
  have h2 := word_column_triality w hcomm 0
  change linearAction w (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ) =
    cycleCoordinates (linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ)) at h2
  have h3 := word_column_triality w hcomm 2
  change linearAction w (Pi.single 3 (1 : ℤ) : Fin 4 → ℤ) =
    cycleCoordinates (linearAction w (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ)) at h3
  rw [h2] at h3
  have hd0 : discriminantLift 0 =
      (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) + Pi.single 2 (1 : ℤ) := by decide
  have hd1 : discriminantLift 1 =
      (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) + Pi.single 3 (1 : ℤ) := by decide
  constructor
  · have hh := wordLinear_discriminant w 0
    rw [hd0, map_add, h2] at hh
    intro i
    exact congrFun hh i
  · have hh := wordLinear_discriminant w 1
    rw [hd1, map_add, h3] at hh
    intro i
    exact congrFun hh i

end SymmetricSubgroupAsymptotics.CFSGTrialityD4WordDiscriminant
