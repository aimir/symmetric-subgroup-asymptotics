import SymmetricSubgroupAsymptotics.CFSGTwistedDFieldDiagramIntertwining

/-! The SAME actual natural matrix image of the original tensor lattice
is preserved by the diagram--field twist. Its genuine semilinear image
equivalence is constructed explicitly, including its inverse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDImageTwist
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFieldTwist CFSGTwistedDFieldDiagramIntertwining
open CFSG.Models.Chevalley CFSGSerreDiagram
variable (K : Type) [Field K]

theorem matrixTwist_inverse (s : ℕ) (σ : K ≃+* K) (M : Mat K (s + 2)) :
    matrixTwist K s σ (matrixTwist K s σ.symm M) = M := by
  ext i j
  change σ (σ.symm (M ((CFSGOrthogonalDGenerationForkTorus.flip s).symm
    ((CFSGOrthogonalDGenerationForkTorus.flip s).symm i))
    ((CFSGOrthogonalDGenerationForkTorus.flip s).symm
      ((CFSGOrthogonalDGenerationForkTorus.flip s).symm j)))) = M i j
  simp only [CFSGOrthogonalDGenerationForkTorus.flip, Equiv.symm_swap,
    Equiv.swap_apply_self, RingEquiv.apply_symm_apply]

theorem matrixTwist_smul (s : ℕ) (σ : K ≃+* K) (a : K) (M : Mat K (s + 2)) :
    matrixTwist K s σ (a • M) = σ a • matrixTwist K s σ M := by
  ext i j
  exact σ.map_mul a (M ((CFSGOrthogonalDGenerationForkTorus.flip s).symm i)
    ((CFSGOrthogonalDGenerationForkTorus.flip s).symm j))

theorem range_preserves (s : ℕ) (σ : K ≃+* K) (M : Mat K (s + 4))
    (hM : M ∈ (orthogonalBaseChange K (s + 4) (by omega)).range) :
    matrixTwist K (s + 2) σ M ∈ (orthogonalBaseChange K (s + 4) (by omega)).range := by
  obtain ⟨x, rfl⟩ := hM
  refine ⟨spaceEquiv (CartanMatrix.D (s + 4)) K (dPermutation (s + 4))
    (d_preserves (s + 4)) (CFSGSerreField.semilinearEquiv (CartanMatrix.D (s + 4)) K σ x), ?_⟩
  exact baseChange_field_diagram K s σ x

local instance (σ : K ≃+* K) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : K ≃+* K) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

def rangeTwist (s : ℕ) (σ : K ≃+* K) :
    (orthogonalBaseChange K (s + 4) (by omega)).range ≃ₛₗ[σ.toRingHom]
      (orthogonalBaseChange K (s + 4) (by omega)).range where
  toFun M := ⟨matrixTwist K (s + 2) σ M.val, range_preserves K s σ M.val M.property⟩
  invFun M := ⟨matrixTwist K (s + 2) σ.symm M.val, range_preserves K s σ.symm M.val M.property⟩
  left_inv M := by
    apply Subtype.ext
    simpa only [RingEquiv.symm_symm] using matrixTwist_inverse K (s + 2) σ.symm M.val
  right_inv M := Subtype.ext (matrixTwist_inverse K (s + 2) σ M.val)
  map_add' M N := Subtype.ext ((matrixTwist K (s + 2) σ).map_add M.val N.val)
  map_smul' a M := Subtype.ext (matrixTwist_smul K (s + 2) σ a M.val)

end SymmetricSubgroupAsymptotics.CFSGTwistedDImageTwist
