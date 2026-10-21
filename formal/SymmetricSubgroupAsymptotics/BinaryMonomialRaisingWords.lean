import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingProducts
import SymmetricSubgroupAsymptotics.BinaryThreeVariablePairMonomialWidth
import SymmetricSubgroupAsymptotics.ModuleLeadingOperatorWords

/-! Explicit short paths for the common-shear monomial order. A path
first uses one pointwise kernel shear when crossing layers, and then
removes the unwanted variables. No search for module generators occurs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryMonomialRaisingWords

open BinaryElementaryPairMonomialWidth
open BinaryBooleanFourPolynomialCoordinates

private instance (s : Finset (Fin 4)) :
    Decidable (BinaryThreeVariablePairMonomialWidth.Allowed s) := by
  unfold BinaryThreeVariablePairMonomialWidth.Allowed
  infer_instance

inductive Op where
  | derivative (i : Fin 4)
  | shear (b : Fin 16)
  deriving DecidableEq

def differenceIndex (a b : Fin 16) : Fin 16 :=
  ⟨(a.val &&& (15 - b.val)) % 16, Nat.mod_lt _ (by decide)⟩

def step (op : Op) (a : Monomial) : Option Monomial :=
  match op with
  | .derivative i => if i ∈ support a.2 then some (a.1, removeIndex i a.2) else none
  | .shear b => if a.1 = true ∧ BinaryThreeVariablePairMonomialWidth.Allowed (support b) ∧
      Disjoint (support b) (support a.2) then some (false, unionIndex b a.2) else none

def path (a b : Monomial) : List Op :=
  let ds := ((List.ofFn fun i : Fin 4 => i).filter
    (fun i => decide (i ∈ support a.2 \ support b.2))).map Op.derivative
  if a.1 = true ∧ b.1 = false then Op.shear (differenceIndex b.2 a.2) :: ds else ds

/-- The certificate follows a prescribed path of length at most five,
for each of the 32 by 32 monomial pairs. -/
theorem path_valid : ∀ a b : Monomial,
    BinaryThreeVariablePairMonomialWidth.Raises a b →
      ModuleLeadingOperatorWords.run step (path a b) a = some b := by decide

def index : Monomial ≃ Fin 32 where
  toFun a := if a.1 then ⟨16 + a.2.val, by omega⟩ else ⟨a.2.val, by omega⟩
  invFun a := (decide (16 ≤ a.val), ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩)
  left_inv := by decide
  right_inv := by decide

def RaisesIndex (a b : Fin 32) : Prop :=
  BinaryThreeVariablePairMonomialWidth.Raises (index.symm a) (index.symm b)

theorem raisesIndex_refl (a : Fin 32) : RaisesIndex a a :=
  BinaryThreeVariablePairMonomialWidth.raises_refl _

theorem antichain_index_card_le_six (s : Finset (Fin 32))
    (hs : IsAntichain RaisesIndex (s : Set (Fin 32))) : s.card ≤ 6 := by
  classical
  let t := s.image index.symm
  have ht : IsAntichain BinaryThreeVariablePairMonomialWidth.Raises (t : Set Monomial) := by
    intro a ha b hb hne hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact hs hi hj (fun he => hne (congrArg index.symm he)) hr
  calc
    s.card = t.card := (Finset.card_image_of_injOn index.symm.injective.injOn).symm
    _ ≤ 6 := BinaryThreeVariablePairMonomialWidth.antichain_card_le_six t ht

end SymmetricSubgroupAsymptotics.BinaryMonomialRaisingWords
