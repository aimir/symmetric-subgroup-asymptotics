import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainRoots

/-! Genuine original fixed-root parameter membership and commutator
lifting to the SAME Derived image. These lemmas allow natural relative
root calculations without postulating relations on the source model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDImageCommutators
open CFSG.Models.Chevalley CFSGSerreFixedRootElements CFSGSerreOrdinaryTwists
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedA2
open CFSGTwistedDFixedCentralCocycle CFSGTwistedDDerivedPairedRoots

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

theorem fixed_node_root_mem_preimage (s : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin (s + 4)) (hi : CFSG.Models.dTwist i = i)
    (t : q.Extension 2) (ht : definingFieldAutomorphism q 2 t = t) :
    CFSGTwistedDPairedRootImages.naturalRoot s q neg i t ∈ naturalFixedPreimage s q := by
  let x := fixedRoot (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) neg i t hi (by simpa only [definingFieldAutomorphism_apply] using ht)
  refine ⟨x, ?_⟩
  exact CFSGTwistedDPairedRootImages.root_image s q neg i t

theorem commutator_mem_derived_preimage (s : ℕ) (q : CFSG.PrimePower)
    (u v : elementaryRootGroup (q.Extension 2) (s + 4))
    (hu : u ∈ naturalFixedPreimage s q) (hv : v ∈ naturalFixedPreimage s q) :
    ⁅u, v⁆ ∈ naturalDerivedPreimage s q := by
  obtain ⟨g, hg⟩ := hu
  obtain ⟨h, hh⟩ := hv
  let d := derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) g h
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  refine ⟨d, ?_⟩
  rw [derivedImageAction_apply]
  have hd : d.val = ⁅g, h⁆ := rfl
  rw [hd, map_commutatorElement, hg, hh]
  exact (map_commutatorElement ν u v).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDImageCommutators
