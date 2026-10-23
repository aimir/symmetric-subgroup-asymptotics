import SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCube

/-! The degree-one middle roots form an actual three-direction cube.
The two small closed checks concern only eight integral root vectors and
three outer directions; they are not finite-field action tables. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCubeStrings
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootCover CFSGTrialityD4MiddleCube

theorem positive_middle_one_eq_cube (k : Roots (CartanMatrix.D 4))
    (hk : ∀ i, 0 ≤ k.val i) (hmid : k.val 1 = 1) : ∃ a : Cube, cubeRoot a = k := by
  obtain ⟨h0, h1, h2, h3⟩ := positive_coordinate_bounds k hk
  have hp0 := hk 0
  have hp2 := hk 2
  have hp3 := hk 3
  let a : Cube := ![⟨(k.val 0).toNat, by omega⟩,
    ⟨(k.val 2).toNat, by omega⟩, ⟨(k.val 3).toNat, by omega⟩]
  refine ⟨a, Subtype.ext ?_⟩
  funext i
  fin_cases i
  · change ((k.val 0).toNat : ℤ) = k.val 0
    exact Int.toNat_of_nonneg hp0
  · change 1 = k.val 1
    exact hmid.symm
  · change ((k.val 2).toNat : ℤ) = k.val 2
    exact Int.toNat_of_nonneg hp2
  · change ((k.val 3).toNat : ℤ) = k.val 3
    exact Int.toNat_of_nonneg hp3

theorem cube_outer_pairing : ∀ (a : Cube) (j : Fin 3),
    integerPairing (CartanMatrix.D 4) (cubeRoot a).val (shortRoot 0 j).val =
      2 * ((a j).val : ℤ) - 1 := by
  decide

theorem cube_update_val : ∀ (a : Cube) (j : Fin 3), a j = 0 →
    (cubeRoot (Function.update a j 1)).val = (cubeRoot a).val + (shortRoot 0 j).val := by
  decide

end SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCubeStrings
