import SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath
import SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators
import SymmetricSubgroupAsymptotics.SixPointTernaryQuarterTurnNormalGenerators

/-! Explicit coordinates carry the two proper binary uppers into the
existing axes/quarter-turn models. Each finite receipt checks only the
72 fixed model elements on six points; no image search is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleProperUpperModelCovers
open SemidirectProduct
open TwoTripleFullUpperForcesFullWreath

private def coordinates : Model ≃ ((ZMod 3 × ZMod 3) × (Binary × Binary)) × Binary where
  toFun g := (((g.left.1.left.toAdd,g.left.2.left.toAdd),(g.left.1.right,g.left.2.right)),g.right)
  invFun p := ⟨(⟨Multiplicative.ofAdd p.1.1.1,p.1.2.1⟩,
    ⟨Multiplicative.ofAdd p.1.1.2,p.1.2.2⟩),p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance : Fintype Model := Fintype.ofEquiv _ coordinates.symm

def axesWitness (g : Model) : SixPointTernaryAxesNormalGenerators.Model :=
  (⟨Multiplicative.ofAdd (g.left.2.left.toAdd + g.left.1.left.toAdd),g.left.1.right⟩,
   ⟨Multiplicative.ofAdd (g.left.2.left.toAdd - g.left.1.left.toAdd),g.left.1.right*g.right⟩)

private theorem axes_points : ∀ (g : Model) (x : Fin 6),
    TwoTripleBinaryUpperRecognition.total (upper g) = 1 →
      SixPointTernaryAxesNormalGenerators.literalAction (axesWitness g) x =
        SixPairLocalWreathSocles.literalAction g x := by decide +kernel

theorem axes_cover (g : Model)
    (h : TwoTripleBinaryUpperRecognition.total (upper g) = 1) :
    SixPointTernaryAxesNormalGenerators.literalAction (axesWitness g) =
      SixPairLocalWreathSocles.literalAction g := Equiv.ext (fun x => axes_points g x h)

def quarterWitness (g : Model) : SixPointTernaryQuarterTurnNormalGenerators.Model :=
  ⟨Multiplicative.ofAdd ![g.left.2.left.toAdd,g.left.1.left.toAdd],
    Multiplicative.ofAdd (if g.right = 1 then
      (if g.left.1.right = 1 then 0 else 2) else
      (if g.left.1.right = 1 then 3 else 1))⟩

private theorem quarter_points : ∀ (g : Model) (x : Fin 6),
    TwoTripleBinaryUpperRecognition.quarterCharacter (upper g) = 1 →
      SixPointTernaryQuarterTurnNormalGenerators.literalAction (quarterWitness g) x =
        SixPairLocalWreathSocles.literalAction g x := by decide +kernel

theorem quarter_cover (g : Model)
    (h : TwoTripleBinaryUpperRecognition.quarterCharacter (upper g) = 1) :
    SixPointTernaryQuarterTurnNormalGenerators.literalAction (quarterWitness g) =
      SixPairLocalWreathSocles.literalAction g := Equiv.ext (fun x => quarter_points g x h)

theorem quarter_swap : ∀ g : Model, g.right = C2Wreath.gen →
    (quarterWitness g).right = SixPointTernaryQuarterTurnNormalGenerators.gen ∨
      (quarterWitness g).right = SixPointTernaryQuarterTurnNormalGenerators.gen⁻¹ := by decide +kernel

theorem swap_of_point : ∀ g : Model, SixPairLocalWreathSocles.literalAction g 0 = 1 →
    g.right = C2Wreath.gen := by decide +kernel

end SymmetricSubgroupAsymptotics.TwoTripleProperUpperModelCovers
