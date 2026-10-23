import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns

/-! The actual roots fixed by triality are precisely the six signed
long roots, and every nonfixed root is a signed short root. This uses
the proved positive-root cover and literal triality orbit formulas. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4InvariantRoots
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGNormTwoGeckColumns
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootCover
open CFSGNormTwoCartanDiagramRoots CFSGIntegralNormTwoSigns CFSGSerreDiagram

abbrev negativeRoot (k : Roots (CartanMatrix.D 4)) :=
  negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite k

abbrev diagramRoot := rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves

def signedLongRoot (neg : Bool) (s : Fin 3) : Roots (CartanMatrix.D 4) :=
  if neg then negativeRoot (longRoot s) else longRoot s

def signedShortRoot (neg : Bool) (s j : Fin 3) : Roots (CartanMatrix.D 4) :=
  if neg then negativeRoot (shortRoot s j) else shortRoot s j

theorem negativeRoot_involutive (k : Roots (CartanMatrix.D 4)) :
    negativeRoot (negativeRoot k) = k := by
  apply Subtype.ext
  simp only [negativeRoot, negative_val, neg_neg]

theorem negativeRoot_injective : Function.Injective negativeRoot :=
  (show Function.Involutive negativeRoot from negativeRoot_involutive).injective

theorem diagramRoot_negative (k : Roots (CartanMatrix.D 4)) :
    diagramRoot (negativeRoot k) = negativeRoot (diagramRoot k) := by
  apply Subtype.ext
  simp only [diagramRoot, negativeRoot, rootPermutation_val, negative_val, map_neg]

theorem diagramRoot_negative_fixed_iff (k : Roots (CartanMatrix.D 4)) :
    diagramRoot (negativeRoot k) = negativeRoot k ↔ diagramRoot k = k := by
  rw [diagramRoot_negative]
  constructor
  · exact fun h => negativeRoot_injective h
  · exact congrArg negativeRoot

theorem signed_root_cover (k : Roots (CartanMatrix.D 4)) :
    (∃ (neg : Bool) (s j : Fin 3), k = signedShortRoot neg s j) ∨
      ∃ (neg : Bool) (s : Fin 3), k = signedLongRoot neg s := by
  rcases norm_two_coordinates_one_sign (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (fun i => by rw [CartanMatrix.D_diag 4 i]; exact even_two)
      (CartanMatrix.D_off_diag_nonpos 4) k.val k.property with hk | hk
  · rcases positive_root_cover k hk with ⟨s, j, he⟩ | ⟨s, he⟩
    · exact Or.inl ⟨false, s, j, he⟩
    · exact Or.inr ⟨false, s, he⟩
  · have hn : ∀ i, 0 ≤ (negativeRoot k).val i := by
      intro i
      change 0 ≤ (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite k).val i
      rw [negative_val]
      exact neg_nonneg.mpr (hk i)
    rcases positive_root_cover (negativeRoot k) hn with ⟨s, j, he⟩ | ⟨s, he⟩
    · left
      refine ⟨true, s, j, ?_⟩
      have hh := congrArg negativeRoot he
      rw [negativeRoot_involutive] at hh
      exact hh
    · right
      refine ⟨true, s, ?_⟩
      have hh := congrArg negativeRoot he
      rw [negativeRoot_involutive] at hh
      exact hh

theorem short_root_not_fixed (s j : Fin 3) : diagramRoot (shortRoot s j) ≠ shortRoot s j := by
  intro he
  rw [short_triality] at he
  have hcoord := congrArg Subtype.val he
  have hne : ∀ s j : Fin 3, shortCoordinates s (cycle j) ≠ shortCoordinates s j := by decide
  exact hne s j hcoord

theorem signed_long_fixed (neg : Bool) (s : Fin 3) :
    diagramRoot (signedLongRoot neg s) = signedLongRoot neg s := by
  cases neg
  · exact long_triality s
  · exact (diagramRoot_negative_fixed_iff (longRoot s)).mpr (long_triality s)

theorem fixed_root_signed_long (k : Roots (CartanMatrix.D 4)) (hk : diagramRoot k = k) :
    ∃ (neg : Bool) (s : Fin 3), k = signedLongRoot neg s := by
  rcases signed_root_cover k with ⟨neg, s, j, rfl⟩ | hl
  · cases neg
    · exact False.elim (short_root_not_fixed s j hk)
    · exact False.elim (short_root_not_fixed s j
        ((diagramRoot_negative_fixed_iff (shortRoot s j)).mp hk))
  · exact hl

theorem nonfixed_root_signed_short (k : Roots (CartanMatrix.D 4)) (hk : diagramRoot k ≠ k) :
    ∃ (neg : Bool) (s j : Fin 3), k = signedShortRoot neg s j := by
  rcases signed_root_cover k with hs | ⟨neg, s, rfl⟩
  · exact hs
  · exact False.elim (hk (signed_long_fixed neg s))

end SymmetricSubgroupAsymptotics.CFSGTrialityD4InvariantRoots
