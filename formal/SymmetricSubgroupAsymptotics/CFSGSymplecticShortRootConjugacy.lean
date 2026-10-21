import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveShortRoot
import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstTorusShortExtraction

/-! All nonidentity elements of the actual projective short-root group
are conjugate by actual coordinate-torus words. This is valid over
every field, including orders two and three. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem projectiveShort_nonidentity_conjugate (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (a b : projectiveShortRoot K r) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ z : elementaryProjective K (r + 1),
      z * (a : elementaryProjective K (r + 1)) * z⁻¹ = b := by
  obtain ⟨u, hu⟩ := a.property
  obtain ⟨v, hv⟩ := b.property
  have hu0 : u.toAdd ≠ 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    rw [← hu, show u = 1 from congrArg Multiplicative.ofAdd hz, map_one]
    rfl
  have hv0 : v.toAdd ≠ 0 := by
    intro hz
    apply hb
    apply Subtype.ext
    rw [← hv, show v = 1 from congrArg Multiplicative.ofAdd hz, map_one]
    rfl
  let g : Kˣ := Units.mk0 (u.toAdd / v.toAdd) (div_ne_zero hu0 hv0)
  have hparam : (g : K)⁻¹ * u.toAdd = v.toAdd := by
    change (u.toAdd / v.toAdd)⁻¹ * u.toAdd = v.toAdd
    field_simp [hu0, hv0]
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  refine ⟨pi (firstTorus K r g), ?_⟩
  rw [← hu, ← hv]
  change pi (firstTorus K r g) * pi (initialShortRoot K r u.toAdd) *
    (pi (firstTorus K r g))⁻¹ = pi (initialShortRoot K r v.toAdd)
  rw [← map_inv, ← map_mul, ← map_mul, firstTorus_short_conjugation K r hr g, hparam]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
