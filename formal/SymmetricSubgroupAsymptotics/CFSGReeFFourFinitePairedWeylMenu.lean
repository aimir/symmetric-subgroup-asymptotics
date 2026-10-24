import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedModelWords

/-! Sixteen literal paired-word lattice actions cover every paired word.
Only the two left-generator transitions on the sixteen 6-by-6 integral
matrices are checked finitely. No equality of original group words is
inferred from this lattice-action statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFinitePairedWeylMenu
open CFSGReeFFourFixedWordClassification CFSGReeFFourPairedWordActions
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6WeylChamber
open CFSGSignedCartanReflections CFSGNormTwoCoordinateLatticeWord
open CFSGExceptionalCartanPositiveDefinite

abbrev MenuIndex := Bool × Fin 8

def menuPairedWord (i : MenuIndex) : List Bool :=
  (List.replicate i.2.val [false,true]).flatten ++ if i.1 then [false] else []

def nextIndex (b : Bool) (i : MenuIndex) : MenuIndex :=
  (!i.1, ⟨(if b then 7-i.2.val else 8-i.2.val)%8,Nat.mod_lt _ (by decide)⟩)

private theorem lattice_step : ∀ b : Bool, ∀ i : MenuIndex,
    latticeWord CartanMatrix.E₆ (expandRelative (expandPaired
      (b :: menuPairedWord i))) =
    latticeWord CartanMatrix.E₆ (expandRelative (expandPaired
      (menuPairedWord (nextIndex b i)))) := by decide +kernel

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

theorem menu_step (b : Bool) (i : MenuIndex) :
    linearAction (expandRelative (pairedRelativeWord b)) *
      linearAction (expandRelative (expandPaired (menuPairedWord i))) =
    linearAction (expandRelative (expandPaired (menuPairedWord (nextIndex b i)))) := by
  have h := linear_eq_of_lattice_eq _ _ (lattice_step b i)
  simpa only [expandPaired,expandRelative_append,linearAction_append] using h

theorem exists_paired_menu_action (s : List Bool) :
    ∃ i : MenuIndex, linearAction (expandRelative (expandPaired s)) =
      linearAction (expandRelative (expandPaired (menuPairedWord i))) := by
  induction s with
  | nil => exact ⟨(false,0),rfl⟩
  | cons b s ih =>
    obtain ⟨i,hi⟩ := ih
    refine ⟨nextIndex b i,?_⟩
    rw [expandPaired,expandRelative_append,linearAction_append,hi]
    exact menu_step b i

theorem menuIndex_card : Nat.card MenuIndex = 16 := by
  simp [MenuIndex]

end SymmetricSubgroupAsymptotics.CFSGReeFFourFinitePairedWeylMenu
