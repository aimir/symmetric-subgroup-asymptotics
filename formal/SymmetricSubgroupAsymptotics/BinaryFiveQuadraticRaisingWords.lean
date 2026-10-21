import SymmetricSubgroupAsymptotics.BinaryMonomialRaisingWords
import SymmetricSubgroupAsymptotics.BinaryFiveQuadraticPairMonomialWidth

/-! Explicit short paths when five quadratic leading shears are present. A path
first uses one pointwise kernel shear when crossing layers, and then
removes the unwanted variables. No search for module generators occurs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryFiveQuadraticRaisingWords

open BinaryElementaryPairMonomialWidth
open BinaryBooleanFourPolynomialCoordinates
open BinaryMonomialRaisingWords (Op index differenceIndex path)

def step (j : Fin 6) (op : Op) (a : Monomial) : Option Monomial :=
  match op with
  | .derivative i => if i ∈ support a.2 then some (a.1, removeIndex i a.2) else none
  | .shear b => if a.1 = true ∧ BinaryFiveQuadraticPairMonomialWidth.Allowed j (support b) ∧
      Disjoint (support b) (support a.2) then some (false, unionIndex b a.2) else none

/-- The certificate follows a prescribed path of length at most five,
for each of the 32 by 32 monomial pairs. -/
theorem path_valid : ∀ j : Fin 6, ∀ a b : Monomial,
    BinaryFiveQuadraticPairMonomialWidth.Raises j a b →
      ModuleLeadingOperatorWords.run (step j) (path a b) a = some b := by decide

def RaisesIndex (j : Fin 6) (a b : Fin 32) : Prop :=
  BinaryFiveQuadraticPairMonomialWidth.Raises j (index.symm a) (index.symm b)

theorem raisesIndex_refl (j : Fin 6) (a : Fin 32) : RaisesIndex j a a :=
  BinaryFiveQuadraticPairMonomialWidth.raises_refl j _

theorem antichain_index_card_le_seven (j : Fin 6) (s : Finset (Fin 32))
    (hs : IsAntichain (RaisesIndex j) (s : Set (Fin 32))) : s.card ≤ 7 := by
  classical
  let t := s.image index.symm
  have ht : IsAntichain (BinaryFiveQuadraticPairMonomialWidth.Raises j) (t : Set Monomial) := by
    intro a ha b hb hne hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact hs hi hj (fun he => hne (congrArg index.symm he)) hr
  calc
    s.card = t.card := (Finset.card_image_of_injOn index.symm.injective.injOn).symm
    _ ≤ 7 := BinaryFiveQuadraticPairMonomialWidth.antichain_card_le_seven j t ht

end SymmetricSubgroupAsymptotics.BinaryFiveQuadraticRaisingWords
