import SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordStabilizer

/-! The two actual outer-root possibilities determine all four columns
of a triality-commuting word fixing the central root. Its full integral
action is the identity or the checked relative word SLSLS. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordMatrix
open CFSGTrialityD4NormTwo CFSGTrialityD4InvariantRoots CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4WordDiscriminant CFSGTrialityD4FixedWeylPilot
open CFSGTrialityD4CentralWordStabilizer CFSGNormTwoGeckColumns
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections

theorem central_fixed_matrix_cases (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k))
    (hcentral : rootAction w (Index 1) = (Index 1 : Roots (CartanMatrix.D 4))) :
    latticeWord (CartanMatrix.D 4) w = 1 ∨
      latticeWord (CartanMatrix.D 4) w = -latticeStep (CartanMatrix.D 4) 1 := by
  have h1 : linearAction w (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) = Pi.single 1 (1 : ℤ) := by
    have he := wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w (Index 1)
    change linearAction w (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) =
      (rootAction w (Index 1)).val at he
    rw [hcentral] at he
    exact he
  have h2 := word_column_triality w hcomm 0
  change linearAction w (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ) =
    cycleCoordinates (linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ)) at h2
  have h3 := word_column_triality w hcomm 2
  change linearAction w (Pi.single 3 (1 : ℤ) : Fin 4 → ℤ) =
    cycleCoordinates (linearAction w (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ)) at h3
  have hcolumn (i : Fin 4) : latticeWord (CartanMatrix.D 4) w *ᵥ
      (Pi.single i (1 : ℤ) : Fin 4 → ℤ) = linearAction w (Pi.single i (1 : ℤ) : Fin 4 → ℤ) :=
    LinearMap.congr_fun (latticeWord_linear (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) w) _
  rcases central_fixed_outer_cases w hcomm hcentral with hpos | hneg
  · have h0 : linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) = Pi.single 0 (1 : ℤ) := by
      have he := wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w (Index 0)
      change linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
        (rootAction w (Index 0)).val at he
      rw [hpos] at he
      exact he
    left
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [hcolumn]
    fin_cases i
    · change linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
        (1 : Matrix (Fin 4) (Fin 4) ℤ) *ᵥ (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ)
      rw [h0]; decide
    · change linearAction w (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) =
        (1 : Matrix (Fin 4) (Fin 4) ℤ) *ᵥ (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ)
      rw [h1]; decide
    · change linearAction w (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ) =
        (1 : Matrix (Fin 4) (Fin 4) ℤ) *ᵥ (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ)
      rw [h2, h0]; decide
    · change linearAction w (Pi.single 3 (1 : ℤ) : Fin 4 → ℤ) =
        (1 : Matrix (Fin 4) (Fin 4) ℤ) *ᵥ (Pi.single 3 (1 : ℤ) : Fin 4 → ℤ)
      rw [h3, h2, h0]; decide
  · have h0 : linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
        -shortCoordinates 1 0 := by
      have he := wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w (Index 0)
      change linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
        (rootAction w (Index 0)).val at he
      rw [hneg] at he
      change linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
        (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite (shortRoot 1 0)).val at he
      rw [negative_val] at he
      exact he
    right
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [hcolumn]
    fin_cases i
    · change linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
        -latticeStep (CartanMatrix.D 4) 1 *ᵥ (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ)
      rw [h0]; decide
    · change linearAction w (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) =
        -latticeStep (CartanMatrix.D 4) 1 *ᵥ (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ)
      rw [h1]; decide
    · change linearAction w (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ) =
        -latticeStep (CartanMatrix.D 4) 1 *ᵥ (Pi.single 2 (1 : ℤ) : Fin 4 → ℤ)
      rw [h2, h0]; decide
    · change linearAction w (Pi.single 3 (1 : ℤ) : Fin 4 → ℤ) =
        -latticeStep (CartanMatrix.D 4) 1 *ᵥ (Pi.single 3 (1 : ℤ) : Fin 4 → ℤ)
      rw [h3, h2, h0]; decide

theorem linearAction_eq_of_latticeWord_eq (u v : List (Fin 4))
    (he : latticeWord (CartanMatrix.D 4) u = latticeWord (CartanMatrix.D 4) v) :
    linearAction u = linearAction v := by
  apply LinearEquiv.toLinearMap_injective
  have hh := congrArg Matrix.mulVecLin he
  rw [latticeWord_linear (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) u,
    latticeWord_linear (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) v] at hh
  exact hh

theorem central_fixed_relative_word (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k))
    (hcentral : rootAction w (Index 1) = (Index 1 : Roots (CartanMatrix.D 4))) :
    ∃ v : List (Fin 4), (v = [] ∨ v = [0,2,3,1,0,2,3,1,0,2,3]) ∧
      linearAction w = linearAction v := by
  rcases central_fixed_matrix_cases w hcomm hcentral with he | he
  · exact ⟨[], Or.inl rfl, linearAction_eq_of_latticeWord_eq w [] he⟩
  · exact ⟨[0,2,3,1,0,2,3,1,0,2,3], Or.inr rfl,
      linearAction_eq_of_latticeWord_eq _ _ (he.trans central_stabilizer_relative_word.symm)⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordMatrix
