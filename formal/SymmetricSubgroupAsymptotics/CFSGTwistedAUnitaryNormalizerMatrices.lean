import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPullbackTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRegularUpper
import SymmetricSubgroupAsymptotics.CFSGRegularUpperNormalizer

/-! An ORIGINAL upper-normalizer lift is triangular in every rank and
every characteristic. All hypotheses of the generic intrinsic-flag
criterion are discharged by literal upper entries and the constructed
regular element of the SAME defining-fixed natural upper subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem pullback_normalizer_upper (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (p : fixedNaturalPullback r q)
    (hp : pullbackSource r q p ∈ Subgroup.normalizer
      (originalUnipotent r q : Set (Fixed r q))) :
    (pullbackMatrix r q p : Mat (q.Extension 2) r).BlockTriangular id := by
  let rho : (Mat (q.Extension 2) r)ˣ →* Mat (q.Extension 2) r := Units.coeHom _
  have hu : ∀ x ∈ naturalUpperUnits q r, (rho x).BlockTriangular id := by
    rintro x ⟨a, ha, rfl⟩
    exact ha.1.1
  have hd : ∀ x ∈ naturalUpperUnits q r, ∀ i, rho x i i = 1 := by
    rintro x ⟨a, ha, rfl⟩ i
    exact ha.1.2 i
  have hregular : ∃ x ∈ naturalUpperUnits q r,
      ∀ i : Fin r, rho x i.castSucc i.succ ≠ 0 := by
    obtain ⟨u, hu⟩ := exists_regular_upper q r
    exact ⟨u.val.val, ⟨u.val, u.property, rfl⟩, hu⟩
  exact CFSGRegularUpperNormalizer.normalizer_upper rho (naturalUpperUnits q r) hu hd hregular
    (pullbackMatrix r q p) (pullback_normalizer_mem_units_normalizer q r hr p hp)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
