import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex

/-! The literal middle-coordinate grading of the D4 roots. Its degree-one
roots contain the eight vertices of a cube; among positive roots, degree
at least two is exactly the highest long root. These are lattice facts,
independent of the characteristic of the eventual coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCube
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootCover

abbrev Cube := Fin 3 → Fin 2

def cubeCoordinates (a : Cube) : Fin 4 → ℤ :=
  ![((a 0).val : ℤ), 1, ((a 1).val : ℤ), ((a 2).val : ℤ)]

private theorem bit_square (a : Fin 2) : (a.val : ℤ)^2 = (a.val : ℤ) := by
  fin_cases a <;> norm_num

theorem cube_norm (a : Cube) :
    integerPairing (CartanMatrix.D 4) (cubeCoordinates a) (cubeCoordinates a) = 2 := by
  have he := energy_formula (cubeCoordinates a)
  change (2*((a 0).val : ℤ)-1)^2 + (2*((a 1).val : ℤ)-1)^2 +
    (2*((a 2).val : ℤ)-1)^2 + 1^2 =
      2 * integerPairing (CartanMatrix.D 4) (cubeCoordinates a) (cubeCoordinates a) at he
  nlinarith [bit_square (a 0), bit_square (a 1), bit_square (a 2)]

def cubeRoot (a : Cube) : Roots (CartanMatrix.D 4) :=
  ⟨cubeCoordinates a, cube_norm a⟩

theorem cubeRoot_middle (a : Cube) : (cubeRoot a).val 1 = 1 := rfl

theorem cubeRoot_positive (a : Cube) (i : Fin 4) : 0 ≤ (cubeRoot a).val i := by
  fin_cases i
  · change 0 ≤ ((a 0).val : ℤ)
    exact_mod_cast Nat.zero_le (a 0).val
  · norm_num [cubeRoot, cubeCoordinates]
  · change 0 ≤ ((a 1).val : ℤ)
    exact_mod_cast Nat.zero_le (a 1).val
  · change 0 ≤ ((a 2).val : ℤ)
    exact_mod_cast Nat.zero_le (a 2).val

theorem cubeRoot_injective : Function.Injective cubeRoot := by
  intro a b hab
  funext i
  have h0 := congrArg (fun k : Roots (CartanMatrix.D 4) => k.val 0) hab
  have h2 := congrArg (fun k : Roots (CartanMatrix.D 4) => k.val 2) hab
  have h3 := congrArg (fun k : Roots (CartanMatrix.D 4) => k.val 3) hab
  change ((a 0).val : ℤ) = ((b 0).val : ℤ) at h0
  change ((a 1).val : ℤ) = ((b 1).val : ℤ) at h2
  change ((a 2).val : ℤ) = ((b 2).val : ℤ) at h3
  apply Fin.ext
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h2
  · exact_mod_cast h3

theorem positive_middle_ge_two_eq_highest (k : Roots (CartanMatrix.D 4))
    (hk : ∀ i, 0 ≤ k.val i) (hmid : 2 ≤ k.val 1) : k = longRoot 2 := by
  rcases positive_root_cover k hk with ⟨s, j, rfl⟩ | ⟨s, rfl⟩
  · fin_cases s <;> fin_cases j <;>
      norm_num [shortRoot, shortCoordinates] at hmid
  · fin_cases s
    · norm_num [longRoot, longCoordinates] at hmid
    · norm_num [longRoot, longCoordinates] at hmid
    · rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCube
