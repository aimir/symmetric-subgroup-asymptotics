import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBorelNormalizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus

/-! An actual SL-chain torus on positive coordinates zero and two.
It normalizes the SAME B-unipotent subgroup and leaves coordinate one
unchanged, so its highest-long-root weight is the unrestricted unit g.
No square-span or field-generator assumption is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
variable (K : Type) [Field K]

def thirdIndex (s : ℕ) : Fin (s + 3) := ⟨2, by omega⟩

def centerTorus (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 3) :=
  doubleIntoElementary K (s + 3)
    (CFSGTypeARootTorus.torus (i := (0 : Fin (s + 3))) (j := thirdIndex s)
      (by intro h; have he := congrArg Fin.val h; change 0 = 2 at he; omega) g)

def centerTorusWeight (s : ℕ) (g : Kˣ) : Index (s + 3) → K
  | .inl (.inl i) => if i = 0 then g else if i = thirdIndex s then (g : K)⁻¹ else 1
  | .inl (.inr i) => if i = 0 then (g : K)⁻¹ else if i = thirdIndex s then g else 1
  | .inr _ => 1

theorem centerTorus_val (s : ℕ) (g : Kˣ) :
    ((centerTorus K s g).val : Mat K (s + 3)) = Matrix.diagonal (centerTorusWeight K s g) := by
  change Matrix.fromBlocks
    (Matrix.fromBlocks (CFSGTypeARootTorus.torus _ g).val 0 0
      ((CFSGTypeARootTorus.torus _ g)⁻¹).val.transpose) 0 0 1 = _
  rw [CFSGTypeARootTorus.torus_inv, CFSGTypeARootTorus.torus_coe,
    CFSGTypeARootTorus.torus_coe, Matrix.diagonal_transpose]
  ext x y
  rcases x with (i | i) | ⟨⟩ <;> rcases y with (j | j) | ⟨⟩ <;>
    simp [centerTorusWeight, Matrix.fromBlocks, Matrix.diagonal,
      Matrix.one_apply, Units.val_inv_eq_inv_val, inv_inv]

theorem centerTorus_mem_borel (s : ℕ) (g : Kˣ) : centerTorus K s g ∈ borel K (s + 3) := by
  change (((centerTorus K s g).val : Mat K (s + 3))).BlockTriangular (flagEquiv (s + 3))
  rw [centerTorus_val]
  exact Matrix.blockTriangular_diagonal _

theorem centerTorus_mem_normalizer (s : ℕ) (g : Kˣ) :
    centerTorus K s g ∈ Subgroup.normalizer
      (unipotent K (s + 3) : Set (elementaryRootGroup K (s + 3))) :=
  borel_le_normalizer_unipotent K (s + 3) (centerTorus_mem_borel K s g)

theorem centerTorus_inv (s : ℕ) (g : Kˣ) : (centerTorus K s g)⁻¹ = centerTorus K s g⁻¹ := by
  unfold centerTorus
  rw [← map_inv, CFSGTypeARootTorus.torus_inv]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
