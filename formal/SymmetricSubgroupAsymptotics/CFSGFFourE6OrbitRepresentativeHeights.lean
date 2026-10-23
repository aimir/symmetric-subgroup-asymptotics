import SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightBound
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The NINE orbit parameters are partitioned by their actual heights
after arbitrary relative-Weyl transport and positive orientation. Their
heights may change; their total parameter count remains exactly nine.
The cutoff is the already proved finite lattice-root height bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OrbitRepresentativeHeights
open CFSGFFourE6CentralizerRootPilot CFSGFFourE6CentralizerRootTransport
open CFSGIntegerHeightSign CFSGNormTwoCoordinateRootHeightBound
open CFSGNormTwoCoordinateRootHeightCommutator

def repHeight (r : List (Fin 4)) (j : Fin 9) : Fin (rootHeightBound CartanMatrix.E₆) :=
  ⟨(height (transportedRoot r (representative j)).val.val).toNat-1,by
    have hp := positive_root_height_pos CartanMatrix.E₆
      (transportedRoot r (representative j)).val (transportedRoot r (representative j)).property
    have hb := height_le_rootHeightBound CartanMatrix.E₆ (transportedRoot r (representative j)).val
    omega⟩

theorem repHeight_spec (r : List (Fin 4)) (j : Fin 9) :
    height (transportedRoot r (representative j)).val.val=(repHeight r j).val+1 := by
  have hp := positive_root_height_pos CartanMatrix.E₆
    (transportedRoot r (representative j)).val (transportedRoot r (representative j)).property
  change height (transportedRoot r (representative j)).val.val=
    (((height (transportedRoot r (representative j)).val.val).toNat-1 : ℕ) : ℤ)+1
  omega

abbrev HeightRep (r : List (Fin 4)) (h : Fin (rootHeightBound CartanMatrix.E₆)) :=
  {j : Fin 9 // repHeight r j=h}

def allHeightRepEquiv (r : List (Fin 4)) :
    (Σh : Fin (rootHeightBound CartanMatrix.E₆),HeightRep r h) ≃ Fin 9 :=
  Equiv.sigmaFiberEquiv (repHeight r)

theorem sum_height_rep_card (r : List (Fin 4)) :
    (∑h : Fin (rootHeightBound CartanMatrix.E₆),Nat.card (HeightRep r h))=9 := by
  have hc := Nat.card_congr (allHeightRepEquiv r)
  simpa only [Nat.card_sigma,Nat.card_fin] using hc

theorem product_height_parameter_card (r : List (Fin 4)) (q : ℕ) :
    (∏h : Fin (rootHeightBound CartanMatrix.E₆),q^Nat.card (HeightRep r h))=q^9 := by
  rw [Finset.prod_pow_eq_pow_sum,sum_height_rep_card]

end SymmetricSubgroupAsymptotics.CFSGFFourE6OrbitRepresentativeHeights
