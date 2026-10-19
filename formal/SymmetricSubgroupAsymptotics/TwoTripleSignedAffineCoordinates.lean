import SymmetricSubgroupAsymptotics.TwoTripleSignedUpperLinearAction
import SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart

/-! The actual nested two-triple wreath is the signed affine ternary plane.
This is an explicit group-coordinate equivalence, including offset lifts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleSignedAffineCoordinates
open SemidirectProduct TwoTripleSignedUpperLinearAction

abbrev linearAction := TernaryMonomialCocycle.linearAction
  blocks coefficient coefficient_one coefficient_mul
abbrev Affine := LinearSemidirectCoprimeSocleBounds.Model linearAction
abbrev Wreath := TwoTripleFullUpperForcesFullWreath.Model

private def wreathCoordinates : Wreath ≃
    ((ZMod 3 × Binary) × (ZMod 3 × Binary)) × Binary where
  toFun g := (((g.left.1.left.toAdd,g.left.1.right),
    (g.left.2.left.toAdd,g.left.2.right)),g.right)
  invFun p := ⟨(⟨Multiplicative.ofAdd p.1.1.1,p.1.1.2⟩,
    ⟨Multiplicative.ofAdd p.1.2.1,p.1.2.2⟩),p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance affineCoordinateWreathFintype : Fintype Wreath :=
  Fintype.ofEquiv _ wreathCoordinates.symm

def toAffine (g : Wreath) : Affine :=
  ⟨Multiplicative.ofAdd ![g.left.1.left.toAdd,g.left.2.left.toAdd],
    TwoTripleFullUpperForcesFullWreath.upper g⟩

def fromAffine (g : Affine) : Wreath :=
  ⟨(⟨Multiplicative.ofAdd (g.left.toAdd 0),g.right.left.1⟩,
    ⟨Multiplicative.ofAdd (g.left.toAdd 1),g.right.left.2⟩),g.right.right⟩

def equiv : Wreath ≃* Affine where
  toFun := toAffine
  invFun := fromAffine
  left_inv := by
    rintro ⟨⟨⟨a,s⟩,⟨b,t⟩⟩,u⟩
    rfl
  right_inv := by
    rintro ⟨v,u⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> rfl
    · rfl
  map_mul' := by
    intro g h
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      revert g h i
      decide +kernel
    · exact (TwoTripleFullUpperForcesFullWreath.upper).map_mul g h

end SymmetricSubgroupAsymptotics.TwoTripleSignedAffineCoordinates
