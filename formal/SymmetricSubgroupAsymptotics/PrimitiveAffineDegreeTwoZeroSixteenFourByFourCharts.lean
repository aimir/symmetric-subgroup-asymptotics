import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-! Small original-point four-by-four charts. Only the 4 generator images
on 16 points are reduced. These charts do not assert a minimal-block
profile, a zero ternary core, or a quotient-socle bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Consecutive blocks retain the original numbering of every point. -/
def coordinates : Fin 4 × Fin 4 ≃ Fin 16 where
  toFun p := ⟨4 * p.1.val + p.2.val, by omega⟩
  invFun x := (⟨x.val / 4, by omega⟩, ⟨x.val % 4, by omega⟩)
  left_inv := by intro p; apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
  right_inv := by intro x; apply Fin.ext; simp; omega

private def row28Top0 : Equiv.Perm (Fin 4) where
  toFun x := (#[0, 1, 3, 2] : Array (Fin 4))[x.val]!
  invFun x := (#[0, 1, 3, 2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

private def row28Top1 : Equiv.Perm (Fin 4) where
  toFun x := (#[0, 2, 3, 1] : Array (Fin 4))[x.val]!
  invFun x := (#[0, 3, 1, 2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

private def row28Top2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1, 0, 3, 2] : Array (Fin 4))[x.val]!
  invFun x := (#[1, 0, 3, 2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

private def row28Top3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2, 3, 0, 1] : Array (Fin 4))[x.val]!
  invFun x := (#[2, 3, 0, 1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

def row28Tops : Fin 4 → Equiv.Perm (Fin 4) :=
  ![row28Top0, row28Top1, row28Top2, row28Top3]

theorem row28_preserves : ∀ j,
    ProductBlockFrame.Preserves coordinates
      (DegreeTwoZeroSixteenInterfaces.row28Generators j) (row28Tops j) := by
  unfold ProductBlockFrame.Preserves
  decide +kernel

/-- Actual top homomorphism, on the original literal closure. -/
def row28Frame : ProductBlockFrame DegreeTwoZeroSixteenInterfaces.Row28Top
    (Fin 4) (Fin 4) :=
  ProductBlockFrame.ofGenerators coordinates
    DegreeTwoZeroSixteenInterfaces.row28Generators row28Tops row28_preserves

theorem row28_top_range : row28Frame.top.range =
    Subgroup.closure (Set.range row28Tops) :=
  ProductBlockFrame.ofGenerators_top_range coordinates
    DegreeTwoZeroSixteenInterfaces.row28Generators row28Tops row28_preserves

private def row29Top0 : Equiv.Perm (Fin 4) where
  toFun x := (#[0, 1, 3, 2] : Array (Fin 4))[x.val]!
  invFun x := (#[0, 1, 3, 2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

private def row29Top1 : Equiv.Perm (Fin 4) where
  toFun x := (#[0, 2, 3, 1] : Array (Fin 4))[x.val]!
  invFun x := (#[0, 3, 1, 2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

private def row29Top2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1, 0, 3, 2] : Array (Fin 4))[x.val]!
  invFun x := (#[1, 0, 3, 2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

private def row29Top3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2, 3, 0, 1] : Array (Fin 4))[x.val]!
  invFun x := (#[2, 3, 0, 1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

def row29Tops : Fin 4 → Equiv.Perm (Fin 4) :=
  ![row29Top0, row29Top1, row29Top2, row29Top3]

theorem row29_preserves : ∀ j,
    ProductBlockFrame.Preserves coordinates
      (DegreeTwoZeroSixteenInterfaces.row29Generators j) (row29Tops j) := by
  unfold ProductBlockFrame.Preserves
  decide +kernel

/-- Actual top homomorphism, on the original literal closure. -/
def row29Frame : ProductBlockFrame DegreeTwoZeroSixteenInterfaces.Row29Top
    (Fin 4) (Fin 4) :=
  ProductBlockFrame.ofGenerators coordinates
    DegreeTwoZeroSixteenInterfaces.row29Generators row29Tops row29_preserves

theorem row29_top_range : row29Frame.top.range =
    Subgroup.closure (Set.range row29Tops) :=
  ProductBlockFrame.ofGenerators_top_range coordinates
    DegreeTwoZeroSixteenInterfaces.row29Generators row29Tops row29_preserves

/-- Index of the unique perfect matching containing a distinct pair.
Diagonal values are unused. -/
def matchingColor (x y : Fin 4) : Fin 3 :=
  if (x.val + y.val = 1 ∨ x.val + y.val = 5) then 0
  else if (x.val + y.val = 2 ∨ x.val + y.val = 4) then 1 else 2

/-- The three local matchings are labelled by the other top points. -/
def row28MatchingLabel (i : Fin 4) (m : Fin 3) : Fin 4 :=
  (![![3, 2, 1], ![3, 2, 0], ![3, 1, 0], ![1, 2, 0]] : Fin 4 → Fin 3 → Fin 4) i m

theorem row28_matchingLabel_injective (i : Fin 4) :
    Function.Injective (row28MatchingLabel i) := by decide +kernel +revert

theorem row28_matchingLabel_ne (i : Fin 4) (m : Fin 3) :
    row28MatchingLabel i m ≠ i := by decide +kernel +revert

/-- Exact local matching transport on the original sixteen points. -/
theorem row28_matching_covariance : ∀ (j i x y : Fin 4), x ≠ y →
    row28MatchingLabel (row28Tops j i)
      (matchingColor
        (coordinates.symm (DegreeTwoZeroSixteenInterfaces.row28Generators j
          (coordinates (i,x)))).2
        (coordinates.symm (DegreeTwoZeroSixteenInterfaces.row28Generators j
          (coordinates (i,y)))).2) =
    row28Tops j (row28MatchingLabel i (matchingColor x y)) := by
  decide +kernel

/-- The three local matchings are labelled by the other top points. -/
def row29MatchingLabel (i : Fin 4) (m : Fin 3) : Fin 4 :=
  (![![3, 2, 1], ![3, 2, 0], ![3, 1, 0], ![1, 2, 0]] : Fin 4 → Fin 3 → Fin 4) i m

theorem row29_matchingLabel_injective (i : Fin 4) :
    Function.Injective (row29MatchingLabel i) := by decide +kernel +revert

theorem row29_matchingLabel_ne (i : Fin 4) (m : Fin 3) :
    row29MatchingLabel i m ≠ i := by decide +kernel +revert

/-- Exact local matching transport on the original sixteen points. -/
theorem row29_matching_covariance : ∀ (j i x y : Fin 4), x ≠ y →
    row29MatchingLabel (row29Tops j i)
      (matchingColor
        (coordinates.symm (DegreeTwoZeroSixteenInterfaces.row29Generators j
          (coordinates (i,x)))).2
        (coordinates.symm (DegreeTwoZeroSixteenInterfaces.row29Generators j
          (coordinates (i,y)))).2) =
    row29Tops j (row29MatchingLabel i (matchingColor x y)) := by
  decide +kernel

end PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts
end SymmetricSubgroupAsymptotics
