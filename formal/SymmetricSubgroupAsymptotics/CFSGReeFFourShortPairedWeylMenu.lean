import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOrderUpper
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedBruhatNumerics

/-! Sixteen bounded alternating representatives for the original paired
Weyl actions. Only the lattice-action comparisons are checked finitely.
The original fixed-cell cover retains the resulting diagonal residual;
no equality of original group words follows merely from equal actions.
The weighted sum is bookkeeping, not a bound for actual cell fibres. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourFinitePairedWeylMenu CFSGReeFFourFixedWordClassification
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6WeylChamber
open CFSGSignedCartanReflections CFSGNormTwoCoordinateLatticeWord
open CFSGExceptionalCartanPositiveDefinite
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourPairedModelWords CFSGReeFFourFixedOrderUpper

def shortLength (i : Fin 16) : ℕ := if i.val=15 then 8 else (i.val+1)/2

def shortWord (i : Fin 16) : List Bool :=
  (List.range (shortLength i)).map fun j =>
    if i.val%2=1 then decide (j%2=1) else decide (j%2=0)

theorem shortWord_length_le (i : Fin 16) : (shortWord i).length ≤ 8 := by
  simp only [shortWord,List.length_map,List.length_range,shortLength]
  split <;> omega

private theorem lattice_cover : ∀ i : MenuIndex, ∃ j : Fin 16,
    latticeWord CartanMatrix.E₆ (expandRelative (expandPaired (menuPairedWord i))) =
    latticeWord CartanMatrix.E₆ (expandRelative (expandPaired (shortWord j))) := by
  decide +kernel

private theorem linear_eq_of_lattice_eq (v w : List (Fin 6))
    (he : latticeWord CartanMatrix.E₆ v=latticeWord CartanMatrix.E₆ w) :
    linearAction v=linearAction w := by
  apply LinearEquiv.toLinearMap_injective
  exact (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos v).symm.trans
    ((congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ=>M.mulVecLin) he).trans
      (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite
        CartanMatrix.E₆_off_diag_nonpos w))

theorem exists_short_menu_action (s : List Bool) : ∃ i : Fin 16,
    linearAction (expandRelative (expandPaired s)) =
      linearAction (expandRelative (expandPaired (shortWord i))) := by
  obtain ⟨i,hi⟩ := exists_paired_menu_action s
  obtain ⟨j,hj⟩ := lattice_cover i
  exact ⟨j,hi.trans (linear_eq_of_lattice_eq _ _ hj)⟩

def shortModelWord (m : ℕ) (i : Fin 16) : originalModelFixed m :=
  fixedPairedWord m (shortWord i)

theorem exists_short_fixed_cell (m : ℕ) (g : originalModelFixed m) :
    ∃ (u : fixedPositive m) (d : fixedDiagonal m) (i : Fin 16)
      (v : fixedPositive m), g=u.val*d.val*shortModelWord m i*v.val := by
  obtain ⟨u,hu,d,hd,s,v,hv,he⟩ := exists_fixed_four_factor_cell m g
  obtain ⟨i,hi⟩ := exists_short_menu_action s
  let delta := fixedPairedWord m s * (shortModelWord m i)⁻¹
  have hdelta : delta ∈ fixedDiagonal m :=
    equal_action_model_residual_mem (Field m) (expandPaired s)
      (expandPaired (shortWord i)) hi
  refine ⟨⟨u,hu⟩,⟨d*delta,(fixedDiagonal m).mul_mem hd hdelta⟩,
    i,⟨v,hv⟩,he.trans ?_⟩
  dsimp only [delta]
  group

def inversionWeight (i : Fin 16) : ℕ :=
  ((shortWord i).map fun b => if b then 2 else 1).sum

private theorem weight_index : ∀ i : Fin 16, inversionWeight i =
    ![0,1,2,3,3,4,5,6,6,7,8,9,9,10,11,12] i := by
  decide +kernel

theorem weighted_short_menu (q : ℕ) :
    (∑ i : Fin 16, q^(inversionWeight i)) =
      CFSGReeFFourWeightedBruhatNumerics.weightedMenu q := by
  simp only [weight_index]
  norm_num [Fin.sum_univ_succ,
    CFSGReeFFourWeightedBruhatNumerics.weightedMenu]
  <;> ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourShortPairedWeylMenu
