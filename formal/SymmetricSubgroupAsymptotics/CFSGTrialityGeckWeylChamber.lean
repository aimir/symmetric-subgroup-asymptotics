import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleOrbitFlags
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordNormalizer
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns
import Mathlib.Data.ZMod.Basic

/-! A nonidentity actual D4 Weyl word has a negative simple image.
If its action commutes with triality, an entire actual relative simple
orbit is negative. Chamber rigidity is the checked integral D4 result,
not a list of exceptional-group elements. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckWeylChamber
open CFSGSerreDiagram CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckAmbientPositiveSylow CFSGTrialityD4WordDiscriminant
open CFSGTrialityD4InvariantRoots CFSGTrialityGeckSimpleOrbitFlags
open CFSGNormTwoCoordinatePositiveWordNormalizer CFSGTrialityRelativeWordLanguage
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem positive_simple_identity (w : List (Fin 4))
    (hw : ∀ i j, 0 ≤ (rootAction w (Index i)).val j) : linearAction w = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact normalizer_word_identity (ZMod 2) w
    (positive_word_mem_normalizer A (CartanMatrix.D_diag 4) hs hp
      (CartanMatrix.D_off_diag_nonpos 4) (ZMod 2) w hw)

theorem exists_negative_simple (w : List (Fin 4)) (hw : linearAction w ≠ 1) :
    ∃ i : Fin 4, ∀ j, (rootAction w (Index i)).val j ≤ 0 := by
  by_contra hnone
  apply hw
  apply positive_simple_identity w
  intro i
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
      (fun j => by rw [CartanMatrix.D_diag 4 j]; exact even_two)
      (CartanMatrix.D_off_diag_nonpos 4) (rootAction w (Index i)).val
      (rootAction w (Index i)).property with hpos | hneg
  · exact hpos
  · exact False.elim (hnone ⟨i,hneg⟩)

theorem negative_simple_partner (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k))
    (i : Fin 4) (hi : ∀ j, (rootAction w (Index i)).val j ≤ 0) :
    ∀ j, (rootAction w (Index (trialityPermutation i))).val j ≤ 0 := by
  have he : diagramRoot (rootAction w (Index i)) =
      rootAction w (Index (trialityPermutation i)) := by
    rw [hcomm]
    exact congrArg (rootAction w) (diagramRoot_index i)
  intro j
  calc
    _ = (diagramRoot (rootAction w (Index i))).val j :=
      congrArg (fun k : CFSGNormTwoRootPairing.Roots A => k.val j) he.symm
    _ = (rootAction w (Index i)).val (trialityPermutation.symm j) := rfl
    _ ≤ 0 := hi _

private theorem outer_orbit_negative (w : List (Fin 4))
    (h0 : ∀ j, (rootAction w (Index 0)).val j ≤ 0)
    (h2 : ∀ j, (rootAction w (Index 2)).val j ≤ 0)
    (h3 : ∀ j, (rootAction w (Index 3)).val j ≤ 0) :
    ∀ i ∈ orbitWord false, ∀ j, (rootAction w (Index i)).val j ≤ 0 := by
  intro i hi
  have h : i = 0 ∨ i = 2 ∨ i = 3 := by simpa only [orbitWord,Bool.false_eq_true,
    ↓reduceIte,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using hi
  rcases h with rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h3

theorem exists_negative_orbit (w : List (Fin 4)) (hw : linearAction w ≠ 1)
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ a : Bool, ∀ i ∈ orbitWord a, ∀ j, (rootAction w (Index i)).val j ≤ 0 := by
  obtain ⟨i,hi⟩ := exists_negative_simple w hw
  fin_cases i
  · have h2 := negative_simple_partner w hcomm 0 hi
    have h3 := negative_simple_partner w hcomm 2 h2
    exact ⟨false,outer_orbit_negative w hi h2 h3⟩
  · refine ⟨true,?_⟩
    intro i him
    have he : i = 1 := by simpa only [orbitWord,↓reduceIte,List.mem_singleton] using him
    subst i
    exact hi
  · have h3 := negative_simple_partner w hcomm 2 hi
    have h0 := negative_simple_partner w hcomm 3 h3
    exact ⟨false,outer_orbit_negative w h0 hi h3⟩
  · have h0 := negative_simple_partner w hcomm 3 hi
    have h2 := negative_simple_partner w hcomm 0 h0
    exact ⟨false,outer_orbit_negative w h0 h2 hi⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckWeylChamber
