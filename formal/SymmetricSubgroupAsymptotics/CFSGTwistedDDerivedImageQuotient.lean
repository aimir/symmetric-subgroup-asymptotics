import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDPartialFlagGeometry

/-! The exact natural preimage maps onto the SAME original Derived
action image and contains every retained chain/folded-fork test. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedImageQuotient
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedA2
open CFSGTwistedDDerivedPairedRoots CFSGTwistedDDerivedChainRoots
open CFSGTwistedDPartialFlagGeometry CFSGTwistedDPairedRootImages

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def preimageToImage (s : ℕ) (q : CFSG.PrimePower) :
    naturalDerivedPreimage s q →* (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range where
  toFun u := ⟨elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s) u.val, u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

theorem preimageToImage_surjective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Surjective (preimageToImage s q) := by
  intro y
  obtain ⟨g, hg⟩ := y.property
  obtain ⟨u, hu⟩ := CFSGTwistedDFixedCentralCocycle.exists_representative s q g.val
  have hum : u ∈ naturalDerivedPreimage s q := ⟨g, hu.symm⟩
  refine ⟨⟨u, hum⟩, ?_⟩
  apply Subtype.ext
  exact hu.trans hg

theorem test_mem_derived_preimage (s : ℕ) (q : CFSG.PrimePower)
    (i : Fin (s + 2) ⊕ Unit) :
    testRoot (q.Extension 2) s i ∈ naturalDerivedPreimage s q := by
  cases i with
  | inl i => exact chain_mem_derived_preimage s q i
  | inr i =>
    have he : testRoot (q.Extension 2) s (Sum.inr i) = pairedNaturalRoot s q false 1 := by
      apply Subtype.ext
      exact (paired_one_val s q).symm
    rw [he]
    exact paired_mem_derived_preimage s q 1

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedImageQuotient
