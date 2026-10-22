import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentActionTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalUnipotent
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TriangularSimilitude

/-! A lift of an ORIGINAL source normalizer is upper triangular.
The pullback is the actual action pullback; no full unitary realization
or Sylow maximality is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGTwistedA2OriginalRelations

theorem unipotentToOriginalFixed_action (q : CFSG.PrimePower) (u : naturalUnipotent q) :
    twistedFixedAction 2 q (unipotentToOriginalFixed q u) =
      naturalElementaryAction (q.Extension 2) 2 u.val :=
  elementaryToModel_action (q.Extension 2) u.val

theorem pullback_normalizer_conjugate_upper (q : CFSG.PrimePower)
    (p : fixedNaturalPullback 2 q)
    (hp : pullbackSource 2 q p ∈ Subgroup.normalizer
      (originalUnipotent q : Set (OriginalFixedA 2 q)))
    (a b : q.Extension 2) (hab : NormCondition (definingFieldAutomorphism q 2) a b) :
    ∃ c d, NormCondition (definingFieldAutomorphism q 2) c d ∧
      (pullbackMatrix 2 q p : Mat (q.Extension 2) 2) *
        upperArray (definingFieldAutomorphism q 2) a b *
          (↑((pullbackMatrix 2 q p)⁻¹) : Mat (q.Extension 2) 2) =
            upperArray (definingFieldAutomorphism q 2) c d := by
  let u : naturalUnipotent q := ⟨upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) a b, a, b, hab, rfl⟩
  have hu : unipotentToOriginalFixed q u ∈ originalUnipotent q := ⟨u, rfl⟩
  have hc := (Subgroup.mem_normalizer_iff.mp hp (unipotentToOriginalFixed q u)).mp hu
  obtain ⟨v, hv⟩ := hc
  obtain ⟨c, d, hcd, hvparam⟩ := v.property
  refine ⟨c, d, hcd, ?_⟩
  have he := congrArg (twistedFixedAction 2 q) hv
  simp only [map_mul, map_inv, unipotentToOriginalFixed_action] at he
  rw [← pullback_action_eq 2 q p] at he
  have he' : naturalElementaryAction (q.Extension 2) 2
      (pullbackElementary 2 q p * upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) a b *
        (pullbackElementary 2 q p)⁻¹) =
      naturalElementaryAction (q.Extension 2) 2 (upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) c d) := by
    rw [map_mul, map_mul, map_inv]
    change _ = naturalElementaryAction (q.Extension 2) 2 _
    rw [← hvparam]
    exact he.symm
  exact upper_conjugate_of_action_eq _ _ (pullbackElementary 2 q p) a b c d he'

theorem pullback_normalizer_first_column (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (p : fixedNaturalPullback 2 q)
    (hp : pullbackSource 2 q p ∈ Subgroup.normalizer
      (originalUnipotent q : Set (OriginalFixedA 2 q))) :
    (pullbackMatrix 2 q p : Mat (q.Extension 2) 2) 1 0 = 0 ∧
      (pullbackMatrix 2 q p : Mat (q.Extension 2) 2) 2 0 = 0 := by
  apply first_column_zero_of_upper_transport q hq
  intro a b hab
  have hi : pullbackSource 2 q (p⁻¹) ∈ Subgroup.normalizer
      (originalUnipotent q : Set (OriginalFixedA 2 q)) := by
    rw [map_inv]
    exact (Subgroup.normalizer _).inv_mem hp
  obtain ⟨c, d, hcd, he⟩ := pullback_normalizer_conjugate_upper q (p⁻¹) hi a b hab
  refine ⟨c, d, hcd, ?_⟩
  let M := pullbackMatrix 2 q p
  change (↑(M⁻¹) : Mat (q.Extension 2) 2) * upperArray (definingFieldAutomorphism q 2) a b *
    (M : Mat (q.Extension 2) 2) = upperArray (definingFieldAutomorphism q 2) c d at he
  calc
    _ = (M : Mat (q.Extension 2) 2) *
        ((↑(M⁻¹) : Mat (q.Extension 2) 2) * upperArray (definingFieldAutomorphism q 2) a b *
          (M : Mat (q.Extension 2) 2)) := by
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    _ = _ := congrArg (fun A : Mat (q.Extension 2) 2 => (M : Mat (q.Extension 2) 2) * A) he

theorem pullback_normalizer_upper (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (p : fixedNaturalPullback 2 q)
    (hp : pullbackSource 2 q p ∈ Subgroup.normalizer
      (originalUnipotent q : Set (OriginalFixedA 2 q))) :
    (pullbackMatrix 2 q p : Mat (q.Extension 2) 2).BlockTriangular id := by
  obtain ⟨h10, h20⟩ := pullback_normalizer_first_column q hq p hp
  obtain ⟨c, _, hc⟩ := pullbackMatrix_similitude 2 (by decide) q p
  exact CFSGTwistedA2TriangularSimilitude.triangular_of_first_column _
    (definingFieldAutomorphism q 2) (pullbackMatrix 2 q p) c hc h10 h20

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
