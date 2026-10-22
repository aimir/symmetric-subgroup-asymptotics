import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedImageTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalImageCovariance

/-! Original fixed-image natural representatives are projectively fixed:
their genuine natural twist differs by the ACTUAL centre. No fixed
literal representative is inferred without cancelling this cocycle. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedCentralCocycle
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedA2 CFSGSerreOrdinaryTwists
open CFSGTwistedDImageTwist CFSGTwistedDNaturalFieldTwist

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def fixedImageAction (s : ℕ) (q : CFSG.PrimePower) :=
  (orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega)).comp (toModel s q)

def naturalFixedPreimage (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)) :=
  (fixedImageAction s q).range.comap (elementaryImageAction (q.Extension 2) (s + 4) (by omega))

theorem exists_representative (s : ℕ) (q : CFSG.PrimePower) (g : Fixed s q) :
    ∃ u : elementaryRootGroup (q.Extension 2) (s + 4),
      elementaryImageAction (q.Extension 2) (s + 4) (by omega) u = fixedImageAction s q g := by
  have h : fixedImageAction s q g ∈
      (orthogonalImageRepresentation (q.Extension 2) (s + 4) (rank_ge_four s)).range :=
    ⟨toModel s q g, rfl⟩
  rw [orthogonal_action_ranges_eq] at h
  exact h

def preimageToImage (s : ℕ) (q : CFSG.PrimePower) :
    naturalFixedPreimage s q →* (fixedImageAction s q).range where
  toFun u := ⟨elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s) u.val, u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

theorem preimageToImage_surjective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Surjective (preimageToImage s q) := by
  intro y
  obtain ⟨g, hg⟩ := y.property
  obtain ⟨u, hu⟩ := exists_representative s q g
  have hum : u ∈ naturalFixedPreimage s q := ⟨g, hu.symm⟩
  refine ⟨⟨u, hum⟩, ?_⟩
  apply Subtype.ext
  exact hu.trans hg

theorem representative_difference_center (s : ℕ) (q : CFSG.PrimePower) (g : Fixed s q)
    (u : elementaryRootGroup (q.Extension 2) (s + 4))
    (hu : elementaryImageAction (q.Extension 2) (s + 4) (by omega) u = fixedImageAction s q g) :
    u⁻¹ * naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u ∈
      Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) := by
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  let T := rangeTwist (q.Extension 2) s (definingFieldAutomorphism q 2)
  have he : ν (naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u) = ν u := by
    apply LinearEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := T.surjective y
    calc
      _ = T (ν u z) := CFSGTwistedDNaturalImageCovariance.elementary_covariance
        (q.Extension 2) s (definingFieldAutomorphism q 2) u z
      _ = ν u (T z) := by
        change T (elementaryImageAction (q.Extension 2) (s + 4) (by omega) u z) =
          elementaryImageAction (q.Extension 2) (s + 4) (by omega) u (T z)
        rw [hu]
        exact (CFSGTwistedDFixedImageTwist.fixed_image_commutes s q g z).symm
  rw [← elementaryImageAction_ker (q.Extension 2) s]
  change ν (u⁻¹ * naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u) = 1
  calc
    _ = ν u⁻¹ * ν (naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u) :=
      ν.map_mul _ _
    _ = 1 := by rw [map_inv, he, inv_mul_cancel]

theorem naturalFixedPreimage_central_difference (s : ℕ) (q : CFSG.PrimePower)
    (u : elementaryRootGroup (q.Extension 2) (s + 4)) (hu : u ∈ naturalFixedPreimage s q) :
    u⁻¹ * naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u ∈
      Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) := by
  obtain ⟨g, hg⟩ := hu
  exact representative_difference_center s q g u hg.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedCentralCocycle
