import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDCenterFixed
import SymmetricSubgroupAsymptotics.CFSGCentralCocycleDerived

/-! The WHOLE natural preimage of the original Derived action image is
literally fixed. The central cocycle kills commutators and is trivial on
the actual central kernel; no arbitrary projective fixed lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedFixed
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedA2 CFSGSerreOrdinaryTwists
open CFSGTwistedDFixedCentralCocycle CFSGTwistedDNaturalFieldTwist
open CFSGTwistedDDerivedPairedRoots

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

theorem derived_preimage_le_fixed_preimage (s : ℕ) (q : CFSG.PrimePower) :
    naturalDerivedPreimage s q ≤ naturalFixedPreimage s q := by
  intro u hu
  obtain ⟨g, hg⟩ := hu
  exact ⟨g.val, hg⟩

theorem preimage_kernel_fixed (s : ℕ) (q : CFSG.PrimePower)
    (u : naturalFixedPreimage s q)
    (hu : CFSGTwistedDFixedCentralCocycle.preimageToImage s q u = 1) :
    naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u.val = u.val := by
  have hν := congrArg Subtype.val hu
  have hz : u.val ∈ Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) := by
    rw [← elementaryImageAction_ker (q.Extension 2) s]
    exact hν
  exact CFSGTwistedDCenterFixed.center_fixed (q.Extension 2) s
    (definingFieldAutomorphism q 2) u.val hz

theorem image_mem_commutator (s : ℕ) (q : CFSG.PrimePower)
    (u : naturalDerivedPreimage s q) :
    CFSGTwistedDFixedCentralCocycle.preimageToImage s q
        ⟨u.val, derived_preimage_le_fixed_preimage s q u.property⟩ ∈
      commutator (CFSGTwistedDFixedCentralCocycle.fixedImageAction s q).range := by
  let μ := CFSGTwistedDFixedCentralCocycle.fixedImageAction s q
  let η := μ.rangeRestrict
  have hmap : (commutator (Fixed s q)).map η = commutator μ.range := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective η μ.rangeRestrict_surjective]
  obtain ⟨g, hg⟩ := u.property
  have hm : η g.val ∈ commutator μ.range := by
    rw [← hmap]
    exact ⟨g.val, g.property, rfl⟩
  have he : CFSGTwistedDFixedCentralCocycle.preimageToImage s q
      ⟨u.val, derived_preimage_le_fixed_preimage s q u.property⟩ = η g.val := by
    apply Subtype.ext
    exact hg.symm
  exact he.symm ▸ hm

theorem derived_preimage_fixed (s : ℕ) (q : CFSG.PrimePower)
    (u : naturalDerivedPreimage s q) :
    naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u.val = u.val := by
  let v : naturalFixedPreimage s q :=
    ⟨u.val, derived_preimage_le_fixed_preimage s q u.property⟩
  exact CFSGCentralCocycleDerived.fixed_over_commutator
    (naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2))
    (naturalFixedPreimage s q)
    (fun x => naturalFixedPreimage_central_difference s q x.val x.property)
    (CFSGTwistedDFixedCentralCocycle.preimageToImage s q)
    (CFSGTwistedDFixedCentralCocycle.preimageToImage_surjective s q)
    (preimage_kernel_fixed s q) v (image_mem_commutator s q u)

theorem derived_preimage_matrix_fixed (s : ℕ) (q : CFSG.PrimePower)
    (u : naturalDerivedPreimage s q) :
    matrixTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
      (u.val.val : Mat (q.Extension 2) (s + 4)) = (u.val.val : Mat (q.Extension 2) (s + 4)) :=
  congrArg (fun x : elementaryRootGroup (q.Extension 2) (s + 4) => (x.val : Mat (q.Extension 2) (s + 4)))
    (derived_preimage_fixed s q u)

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedFixed
