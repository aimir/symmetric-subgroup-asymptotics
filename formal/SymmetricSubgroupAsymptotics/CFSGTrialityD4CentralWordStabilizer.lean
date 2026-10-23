import SymmetricSubgroupAsymptotics.CFSGTrialityD4WordDiscriminant

/-! A genuine word in the original D4 reflections, commuting with
triality and fixing the central simple root, has just two possible
outer-simple-root images. The mod-two and pairing conditions of the
finite pilot are proved from that same word, not supplied as assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordStabilizer
open CFSGTrialityD4NormTwo CFSGTrialityD4InvariantRoots CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4WordDiscriminant CFSGTrialityD4FixedWeylPilot
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckWeylLatticeLinear

theorem rootAction_injective (w : List (Fin 4)) : Function.Injective (rootAction w) := by
  intro k l he
  apply Subtype.ext
  apply (linearAction w).injective
  rw [wordLinear_root, wordLinear_root]
  exact congrArg Subtype.val he

theorem outer_image_not_fixed (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    diagramRoot (rootAction w (Index 0)) ≠ rootAction w (Index 0) := by
  intro hfixed
  have hc := hcomm (Index 0)
  rw [diagramRoot_index] at hc
  change diagramRoot (rootAction w (Index 0)) = rootAction w (Index 2) at hc
  have he := rootAction_injective w (hc.symm.trans hfixed)
  have hentry := congrArg (fun k : Roots (CartanMatrix.D 4) => k.val 2) he
  change (1 : ℤ) = 0 at hentry
  norm_num at hentry

theorem central_fixed_outer_cases (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k))
    (hcentral : rootAction w (Index 1) = (Index 1 : Roots (CartanMatrix.D 4))) :
    rootAction w (Index 0) = (Index 0 : Roots (CartanMatrix.D 4)) ∨
      rootAction w (Index 0) = negativeRoot (shortRoot 1 0) := by
  obtain ⟨neg, s, j, ha⟩ := nonfixed_root_signed_short (rootAction w (Index 0))
    (outer_image_not_fixed w hcomm)
  have hv : (rootAction w (Index 0)).val = signedShortCoordinates neg s j := by
    rw [ha]
    cases neg
    · rfl
    · change (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (shortRoot s j)).val = -shortCoordinates s j
      rw [negative_val]
      rfl
  have hp := wordRoot_integer_pairing (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index w (Index 0) (Index 1)
  change integerPairing (CartanMatrix.D 4) (rootAction w (Index 0)).val
    (rootAction w (Index 1)).val =
      integerPairing (CartanMatrix.D 4) (Index 0 : Roots (CartanMatrix.D 4)).val
        (Index 1 : Roots (CartanMatrix.D 4)).val at hp
  rw [hcentral] at hp
  have h01 : integerPairing (CartanMatrix.D 4) (Index 0 : Roots (CartanMatrix.D 4)).val
      (Index 1 : Roots (CartanMatrix.D 4)).val = -1 := by
    change integerPairing (CartanMatrix.D 4)
      (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) = -1
    calc
      _ = CartanMatrix.D 4 0 1 := Matrix.toBilin'_single (CartanMatrix.D 4) 0 1
      _ = -1 := by decide
  have hbeta : (Index 1 : Roots (CartanMatrix.D 4)).val = longCoordinates 0 := by
    change (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) = longCoordinates 0
    decide
  rw [hv, h01, hbeta] at hp
  have hd := word_outer_discriminants w hcomm
  have he0 : linearAction w (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) =
      (rootAction w (Index 0)).val :=
    wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w (Index 0)
  rw [he0, hv] at hd
  rcases central_stabilizer_outer_cases neg s j hp hd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left
    change rootAction w (Index 0) = shortRoot 0 0 at ha
    refine ha.trans ?_
    apply Subtype.ext
    decide
  · exact Or.inr ha

end SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordStabilizer
