import SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality
import SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeWeylOrbits
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalPositiveStep

/-! A genuine height-decreasing relative reflection step for every
nonsimple positive E6 root. The positive norm of k+sigma(k) selects an
orbit with positive total simple pairing; the actual commuting orbit
reflections preserve positivity and lower height by that sum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6PositiveOrbitStep
open CFSGTwistedE6DiagramRootOrthogonality CFSGTwistedE6WeylChamber
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreDiagram
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCartanDiagramRoots CFSGNormTwoCartanDiagramWords
open CFSGIntegerPairingPositiveDescent CFSGIntegerHeightSign
open CFSGNormTwoCoordinateOrthogonalPositiveStep CFSGNormTwoCoordinateReflectionSigns

abbrev simplePairing (k : Roots CartanMatrix.E₆) (i : Fin 6) : ℤ :=
  integerPairing CartanMatrix.E₆ k.val (E6Index i:Roots CartanMatrix.E₆).val

def orbitPairing (k : Roots CartanMatrix.E₆) (a : Fin 4) : ℤ :=
  ((orbitWord a).map (simplePairing k)).sum

theorem diagram_partner_simple_pairing (k : Roots CartanMatrix.E₆) (i : Fin 6) :
    simplePairing (diagramRoot k) i=simplePairing k (e6Permutation i) := by
  have he := rootPermutation_pairing CartanMatrix.E₆ e6Permutation e6_preserves
    k (E6Index (e6Permutation i))
  have hs := simple_rootPermutation CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    e6Permutation e6_preserves (e6Permutation i)
  change diagramRoot (E6Index (e6Permutation i))=E6Index (e6Permutation (e6Permutation i)) at hs
  rw [diagramPermutation_involutive] at hs
  change integerPairing CartanMatrix.E₆ (diagramRoot k).val
    (diagramRoot (E6Index (e6Permutation i))).val=_ at he
  rw [hs] at he
  exact he

theorem exists_positive_orbit_pairing (k : Roots CartanMatrix.E₆) (hk : ∀i,0 ≤ k.val i) :
    ∃a : Fin 4,0 < orbitPairing k a := by
  let y := k.val+(diagramRoot k).val
  have hy : ∀i,0 ≤ y i := by
    intro i
    change 0 ≤ k.val i+(diagramRoot k).val i
    rw [diagramRoot_coordinate]
    exact add_nonneg (hk i) (hk _)
  have hnorm : 0 < integerPairing CartanMatrix.E₆ y y := by
    dsimp only [y]
    rw [norm_add CartanMatrix.E₆ CartanMatrix.E₆_transpose,k.property,(diagramRoot k).property]
    by_cases he : k=diagramRoot k
    · rw [←he,k.property]
      norm_num
    · rw [positive_diagram_pair_orthogonal k hk he]
      norm_num
  obtain ⟨i,_,hi⟩ := exists_positive_coordinate_pairing (integerPairing CartanMatrix.E₆) y hy hnorm
  have hc : 0 < simplePairing k i+simplePairing k (e6Permutation i) := by
    change 0 < integerPairing CartanMatrix.E₆ (k.val+(diagramRoot k).val)
      (E6Index i:Roots CartanMatrix.E₆).val at hi
    rw [map_add,LinearMap.add_apply] at hi
    change 0 < simplePairing k i+simplePairing (diagramRoot k) i at hi
    rw [diagram_partner_simple_pairing] at hi
    exact hi
  fin_cases i
  · refine ⟨0,?_⟩
    change 0 < simplePairing k 0+simplePairing k 5 at hc
    change 0 < simplePairing k 0+(simplePairing k 5+0)
    omega
  · refine ⟨3,?_⟩
    change 0 < simplePairing k 1+simplePairing k 1 at hc
    change 0 < simplePairing k 1+0
    omega
  · refine ⟨1,?_⟩
    change 0 < simplePairing k 2+simplePairing k 4 at hc
    change 0 < simplePairing k 2+(simplePairing k 4+0)
    omega
  · refine ⟨2,?_⟩
    change 0 < simplePairing k 3+simplePairing k 3 at hc
    change 0 < simplePairing k 3+0
    omega
  · refine ⟨1,?_⟩
    change 0 < simplePairing k 4+simplePairing k 2 at hc
    change 0 < simplePairing k 2+(simplePairing k 4+0)
    omega
  · refine ⟨0,?_⟩
    change 0 < simplePairing k 5+simplePairing k 0 at hc
    change 0 < simplePairing k 0+(simplePairing k 5+0)
    omega

theorem orbit_word_height (a : Fin 4) (k : Roots CartanMatrix.E₆) :
    height (rootAction (orbitWord a) k).val=height k.val-orbitPairing k a := by
  fin_cases a
  · change height (rootAction [0,5] k).val=height k.val-(simplePairing k 0+(simplePairing k 5+0))
    simpa only [add_zero] using orthogonal_pair_height CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos 0 5 (by decide) k
  · change height (rootAction [2,4] k).val=height k.val-(simplePairing k 2+(simplePairing k 4+0))
    simpa only [add_zero] using orthogonal_pair_height CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos 2 4 (by decide) k
  · change height ((E6Pairing.reflectionPerm (E6Index 3)) k).val=height k.val-(simplePairing k 3+0)
    simpa only [add_zero] using simple_reflection_height CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos 3 k
  · change height ((E6Pairing.reflectionPerm (E6Index 1)) k).val=height k.val-(simplePairing k 1+0)
    simpa only [add_zero] using simple_reflection_height CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos 1 k

theorem orbit_word_nonnegative (a : Fin 4) (k : Roots CartanMatrix.E₆)
    (hk : ∀j,0 ≤ k.val j) (hns : ∀i,k≠(E6Index i:Roots CartanMatrix.E₆)) :
    ∀j,0 ≤ (rootAction (orbitWord a) k).val j := by
  fin_cases a
  · exact orthogonal_pair_nonnegative CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      0 5 (by decide) k hk (hns 0) (hns 5)
  · exact orthogonal_pair_nonnegative CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      2 4 (by decide) k hk (hns 2) (hns 4)
  · exact reflection_nonnegative CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos 3 k hk (hns 3)
  · exact reflection_nonnegative CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos 1 k hk (hns 1)

theorem positive_orbit_step (k : Roots CartanMatrix.E₆) (hk : ∀i,0 ≤ k.val i)
    (hns : ∀i,k≠(E6Index i:Roots CartanMatrix.E₆)) :
    ∃a : Fin 4,(∀i,0 ≤ (rootAction (orbitWord a) k).val i) ∧
      height (rootAction (orbitWord a) k).val<height k.val := by
  obtain ⟨a,ha⟩ := exists_positive_orbit_pairing k hk
  refine ⟨a,orbit_word_nonnegative a k hk hns,?_⟩
  rw [orbit_word_height]
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedE6PositiveOrbitStep
