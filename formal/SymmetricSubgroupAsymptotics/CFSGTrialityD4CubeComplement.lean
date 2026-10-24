import SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCube

/-! Complementary vertices of the actual middle D4 cube. Only opposite
vertices add to the highest root; this is the eight-coordinate geometry
behind the radical's alternating commutator pairing. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4CubeComplement

open CFSGIntegerMatrixPairing CFSGTrialityD4MiddleCube CFSGTrialityD4PositiveRootOrbits

def complement (a : Cube) : Cube := fun j => 1 - a j

theorem complement_involutive : Function.Involutive complement := by
  change ∀ a : Cube, complement (complement a) = a
  decide +kernel

theorem complement_ne (a : Cube) : complement a ≠ a := by
  have h : ∀ b : Cube, complement b ≠ b := by decide +kernel
  exact h a

theorem cube_pairing_eq_neg_one_iff (a b : Cube) :
    integerPairing (CartanMatrix.D 4) (cubeRoot a).val (cubeRoot b).val = -1 ↔
      b = complement a := by
  have h : ∀ c d : Cube,
      integerPairing (CartanMatrix.D 4) (cubeRoot c).val (cubeRoot d).val = -1 ↔
        d = complement c := by decide +kernel
  exact h a b

theorem complementary_root_sum (a : Cube) :
    (cubeRoot a).val + (cubeRoot (complement a)).val = (longRoot 2).val := by
  have h : ∀ b : Cube,
      (cubeRoot b).val + (cubeRoot (complement b)).val = (longRoot 2).val := by decide +kernel
  exact h a

end SymmetricSubgroupAsymptotics.CFSGTrialityD4CubeComplement
