import SymmetricSubgroupAsymptotics.CFSGTwistedASimilitudeCentralRatio
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalDeterminant

/-! Every element of the ORIGINAL fixed-group commutator has an actual
determinant-one isometric natural lift with the same action on the
original integral tensor image. This is containment, not equality with
the full special unitary group and not source faithfulness. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

theorem surjective_commutator_lift {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (x : commutator H) :
    ∃ y : commutator G, f y.val = x.val := by
  have hm : (commutator G).map f = commutator H := by
    change Subgroup.map f (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) =
      (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H)
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  have hx : x.val ∈ (commutator G).map f := by rw [hm]; exact x.property
  obtain ⟨y, hy, he⟩ := hx
  exact ⟨⟨y, hy⟩, he⟩

theorem fixed_unit_isometric (K : Type) [Field K] (r : ℕ) (f : K →+* K)
    (u : (Mat K r)ˣ) (hu : diagramFieldUnitHom K r f u = u) :
    (f.mapMatrix (u : Mat K r)).transpose *
        (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (u : Mat K r) =
      (↑((signedReversalUnit K r)⁻¹) : Mat K r) := by
  have he : (diagramFieldUnitHom K r f u)⁻¹ * u = 1 := by rw [hu, inv_mul_cancel]
  have hh := congrArg (fun v : (Mat K r)ˣ =>
    (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (v : Mat K r)) he
  change (↑((signedReversalUnit K r)⁻¹) : Mat K r) *
      ((↑((diagramFieldUnitHom K r f u)⁻¹) : Mat K r) * (u : Mat K r)) =
    (↑((signedReversalUnit K r)⁻¹) : Mat K r) * 1 at hh
  rw [diagramFieldUnitHom_inv_val] at hh
  simpa only [mul_assoc, Units.inv_mul_cancel_left, mul_one] using hh

theorem original_derived_isometric_lift (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (g : commutator (OriginalFixedA r q)) :
    ∃ u : NaturalElementary (q.Extension 2) r,
      naturalElementaryAction (q.Extension 2) r u = twistedDerivedAction r q g ∧
      Matrix.det (u.val : Mat (q.Extension 2) r) = 1 ∧
        ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
          (u.val : Mat (q.Extension 2) r)).transpose *
            (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) *
              (u.val : Mat (q.Extension 2) r) =
          (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) := by
  obtain ⟨p, hp⟩ := surjective_commutator_lift (pullbackSource r q)
    (pullbackSource_surjective r hr q) g
  refine ⟨pullbackElementary r q p.val, ?_, naturalElementary_det _ _ _, ?_⟩
  · rw [pullback_action_eq, hp]
    rfl
  · exact fixed_unit_isometric (q.Extension 2) r
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom
      (pullbackMatrix r q p.val) (pullback_derived_twist_fixed r hr q p)

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
