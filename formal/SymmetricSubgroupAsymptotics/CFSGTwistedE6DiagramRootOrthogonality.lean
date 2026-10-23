import SymmetricSubgroupAsymptotics.CFSGTwistedE6WeylChamber
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
import Mathlib.Tactic.Ring

/-! Every distinct positive E6 root and its diagram partner are
orthogonal. The proof uses a two-variable anti-invariant lattice norm
identity and the proved norm-two pairing bounds, without a root census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality
open CFSGTwistedE6WeylChamber CFSGSerreDiagram
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoCartanDiagramWords

theorem diagramPermutation_involutive : Function.Involutive e6Permutation := by
  intro i
  fin_cases i <;> decide

theorem diagramPermutation_symm (i : Fin 6) : e6Permutation.symm i=e6Permutation i := by
  apply e6Permutation.injective
  rw [e6Permutation.apply_symm_apply,diagramPermutation_involutive]

theorem diagramRoot_coordinate (k : Roots CartanMatrix.E₆) (i : Fin 6) :
    (diagramRoot k).val i=k.val (e6Permutation i) := by
  change k.val (e6Permutation.symm i)=_
  rw [diagramPermutation_symm]

def antiInvariantVector (a b : ℤ) : Fin 6→ℤ := ![a,0,b,0,-b,-a]

theorem antiInvariant_norm (a b : ℤ) :
    integerPairing CartanMatrix.E₆ (antiInvariantVector a b) (antiInvariantVector a b)=
      4*(a^2-a*b+b^2) := by
  norm_num [antiInvariantVector,integerPairing,Matrix.toBilin'_apply,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,CartanMatrix.E₆]
  ring

theorem root_difference_vector (k : Roots CartanMatrix.E₆) :
    k.val-(diagramRoot k).val=
      antiInvariantVector (k.val 0-k.val 5) (k.val 2-k.val 4) := by
  funext i
  simp only [Pi.sub_apply,diagramRoot_coordinate]
  fin_cases i
  · change k.val 0-k.val 5=k.val 0-k.val 5
    rfl
  · change k.val 1-k.val 1=0
    exact sub_self _
  · change k.val 2-k.val 4=k.val 2-k.val 4
    rfl
  · change k.val 3-k.val 3=0
    exact sub_self _
  · change k.val 4-k.val 2= -(k.val 2-k.val 4)
    ring
  · change k.val 5-k.val 0= -(k.val 0-k.val 5)
    ring

theorem root_difference_norm (k : Roots CartanMatrix.E₆) :
    integerPairing CartanMatrix.E₆ (k.val-(diagramRoot k).val)
      (k.val-(diagramRoot k).val)=
        4*((k.val 0-k.val 5)^2-(k.val 0-k.val 5)*(k.val 2-k.val 4)+
          (k.val 2-k.val 4)^2) := by
  rw [root_difference_vector,antiInvariant_norm]

theorem positive_diagram_pair_orthogonal (k : Roots CartanMatrix.E₆)
    (hk : ∀i,0≤k.val i) (hne : k≠diagramRoot k) :
    integerPairing CartanMatrix.E₆ k.val (diagramRoot k).val=0 := by
  have hpartner : ∀i,0≤(diagramRoot k).val i := by
    intro i
    rw [diagramRoot_coordinate]
    exact hk _
  have hopp : k.val≠ -(diagramRoot k).val := by
    intro he
    have hz : k.val=0 := by
      funext i
      have hi := congrFun he i
      change k.val i= -(diagramRoot k).val i at hi
      have h1 := hk i
      have h2 := hpartner i
      change k.val i=0
      omega
    have hn := k.property
    rw [hz] at hn
    norm_num at hn
  have hinterior := root_pairing_interior CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite k (diagramRoot k) hne hopp
  have hnorm := root_difference_norm k
  rw [norm_sub CartanMatrix.E₆ CartanMatrix.E₆_transpose,k.property,
    (diagramRoot k).property] at hnorm
  rcases hinterior with h|h|h
  · omega
  · exact h
  · omega

end SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality
