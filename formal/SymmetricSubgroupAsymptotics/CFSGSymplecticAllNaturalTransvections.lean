import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalPairingPreservation
import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionActualRoots

/-! Every natural symplectic transvection is an actual original-group
word: conjugate the same long-root element by the checked nonzero-vector
orbit witness. This asserts no intrinsic abstract recognition theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem exists_elementary_natural_transvection (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) (a : K) :
    ∃ u : elementaryRootGroup K (r + 1), ∀ x : Index (r + 1) → K,
      (u.val : Mat K (r + 1)) *ᵥ x = transvection (r + 1) v a x := by
  obtain ⟨g, hg⟩ := exists_elementary_mulVec_first_basis K r hr v hv
  let e : Index (r + 1) → K := Pi.single (Sum.inl (0 : Fin (r + 1))) 1
  refine ⟨g * firstLongRoot K r a * g⁻¹, ?_⟩
  intro x
  have hi : (g.val : Mat K (r + 1)) *ᵥ ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hp := elementary_preserves_pairing (r + 1) g e
    ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x)
  change pairing (r + 1) ((g.val : Mat K (r + 1)) *ᵥ e)
    ((g.val : Mat K (r + 1)) *ᵥ ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x)) = _ at hp
  rw [show (g.val : Mat K (r + 1)) *ᵥ e = v from hg, hi] at hp
  change (((g.val : Mat K (r + 1)) * ((firstLongRoot K r a).val : Mat K (r + 1))) *
    (↑(g.val⁻¹) : Mat K (r + 1))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    firstLongRoot_mulVec_eq_transvection, transvection_apply,
    Matrix.mulVec_add, Matrix.mulVec_smul, hi]
  change x + (a * pairing (r + 1) e ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x)) •
    ((g.val : Mat K (r + 1)) *ᵥ e) = x + (a * pairing (r + 1) v x) • v
  rw [← hp, show (g.val : Mat K (r + 1)) *ᵥ e = v from hg]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
