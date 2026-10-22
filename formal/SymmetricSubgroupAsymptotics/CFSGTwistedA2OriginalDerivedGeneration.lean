import SymmetricSubgroupAsymptotics.CFSGTwistedA2IsometricGeneration

/-! The two ACTUAL original unipotent subgroups generate the ORIGINAL
fixed-source derived group. Actual isometric lifts are eliminated in
natural coordinates, and original rank-two action faithfulness transfers
those exact word images back. No full SU premise or simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreFixedRootElements CFSGTwistedA2OriginalRelations

theorem rootGenerated_eq_commutator (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (t : q.Extension 2) (ht0 : t ≠ 0) (ht : t ^ q.order = -t) :
    rootGenerated q t ht = commutator (OriginalFixedA 2 q) := by
  apply le_antisymm (rootGenerated_le_commutator q hq t ht)
  intro g hg
  obtain ⟨u, hu, _, hform⟩ := original_derived_isometric_lift 2 (by decide) q ⟨g, hg⟩
  have hunat := isometric_mem_rootGenerated q t ht0 ht u hform
  have hm : elementaryToModel (q.Extension 2) u ∈ (rootGenerated q t ht).map
      (fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)) :=
    naturalRootGenerated_map_le_original q t ht ⟨u, hunat, rfl⟩
  obtain ⟨g', hg', he⟩ := hm
  have hgg : g' = g := by
    apply twistedFixedAction_two_injective q
    change naturalAction (q.Extension 2) 2
        (fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) g') =
      twistedFixedAction 2 q g
    rw [he, elementaryToModel_action]
    exact hu
  rwa [hgg] at hg'

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
