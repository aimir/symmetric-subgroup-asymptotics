import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordSubgroup
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalFixedWordChart
import Mathlib.GroupTheory.PGroup

/-! A genuine positive 3-subgroup of the literal ORIGINAL Ree fixed group.
Its exact q^3 count is obtained from explicit fixed words and their actual
closure, not from a supplied exceptional order formula. Derived membership
and a Sylow assertion are separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalPositiveSubgroup
open CFSG.Models.Chevalley CFSGGTwoPositiveSixWord CFSGGTwoPositiveWordSubgroup
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalFixedWordChart CFSGReeGTwoFixedCoordinateArithmetic

/-- Actual intersection of the six-word subgroup with fixed points in Model. -/
def fixedPositiveGroup (m : ℕ) : Subgroup (originalModelFixed m) :=
  (positiveWordGroup (Field m)).comap (originalModelFixed m).subtype

def fixedPositiveChart (m : ℕ) (y : Fin 3 → Field m) : fixedPositiveGroup m :=
  ⟨fixedWord m y, ⟨normalForm (alphaEquiv m) (y 0) (y 1) (y 2),rfl⟩⟩

theorem fixedPositiveChart_injective (m : ℕ) :
    Function.Injective (fixedPositiveChart m) := by
  intro y z h
  exact fixedWord_injective m (congrArg (fun g : fixedPositiveGroup m => g.val) h)

theorem fixedPositiveChart_surjective (m : ℕ) :
    Function.Surjective (fixedPositiveChart m) := by
  intro g
  obtain ⟨y,hy⟩ := fixedWord_covers_words m g.val g.property
  exact ⟨y,Subtype.ext hy⟩

def fixedPositiveEquiv (m : ℕ) : (Fin 3 → Field m) ≃ fixedPositiveGroup m :=
  Equiv.ofBijective (fixedPositiveChart m)
    ⟨fixedPositiveChart_injective m,fixedPositiveChart_surjective m⟩

theorem fixedPositiveGroup_card (m : ℕ) :
    Nat.card (fixedPositiveGroup m)=(3^(2*m+1))^3 := by
  rw [←Nat.card_congr (fixedPositiveEquiv m),Nat.card_fun,Nat.card_fin,field_card]

theorem fixedPositiveGroup_isPGroup (m : ℕ) : IsPGroup 3 (fixedPositiveGroup m) :=
  IsPGroup.of_card ((fixedPositiveGroup_card m).trans (pow_mul 3 (2*m+1) 3).symm)

/-- SAME subgroup transported into the exact fixedSubgroup used in the
original Chevalley.Twisted definition, before taking its derived quotient. -/
def originalPositiveGroup (m : ℕ) : Subgroup
    (fixedSubgroup CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m)) :=
  (fixedPositiveGroup m).map (originalFixedEquiv m).symm.toMonoidHom

theorem originalPositiveGroup_card (m : ℕ) :
    Nat.card (originalPositiveGroup m)=(3^(2*m+1))^3 := by
  have hc : Nat.card (fixedPositiveGroup m)=Nat.card (originalPositiveGroup m) :=
    Nat.card_congr ((originalFixedEquiv m).symm.subgroupMap (fixedPositiveGroup m)).toEquiv
  exact hc.symm.trans (fixedPositiveGroup_card m)

theorem originalPositiveGroup_isPGroup (m : ℕ) : IsPGroup 3 (originalPositiveGroup m) :=
  IsPGroup.of_card ((originalPositiveGroup_card m).trans (pow_mul 3 (2*m+1) 3).symm)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalPositiveSubgroup
