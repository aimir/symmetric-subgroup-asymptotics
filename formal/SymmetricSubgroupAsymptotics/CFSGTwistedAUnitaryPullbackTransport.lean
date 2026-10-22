import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryActionTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedLiftPullback

/-! Faithful actual fixed-action pullbacks in all ranks, and exact
transport of ORIGINAL upper-normalizer conjugation to the literal
natural upper subgroup. Scalar ambiguity is removed by genuine
defining-characteristic p-powers, not by a projective-model premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAIntervalSource CFSG.Models.Chevalley CFSGSerreFixedRootElements

theorem twistedFixedAction_injective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Injective (twistedFixedAction r q) := by
  intro g h he
  have hh := naturalAction_injective (q.Extension 2) r he
  apply Subtype.ext
  exact congrArg (fun u : Model (CartanMatrix.A r) (q.Extension 2) => u.val) hh

theorem pullbackMatrix_injective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Injective (pullbackMatrix r q) := by
  intro p t he
  have helem : pullbackElementary r q p = pullbackElementary r q t := Subtype.ext he
  have hsource : pullbackSource r q p = pullbackSource r q t := by
    apply twistedFixedAction_injective q r
    rw [← pullback_action_eq, ← pullback_action_eq, helem]
  apply Subtype.ext
  exact Prod.ext hsource helem

theorem unipotentToOriginalFixed_action (q : CFSG.PrimePower) (r : ℕ)
    (u : naturalUnipotent r q) :
    twistedFixedAction r q (unipotentToOriginalFixed r q u) =
      naturalElementaryAction (q.Extension 2) r u.val :=
  elementaryToModel_action (q.Extension 2) r u.val

theorem pullback_normalizer_conjugate_upper (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (p : fixedNaturalPullback r q)
    (hp : pullbackSource r q p ∈ Subgroup.normalizer
      (originalUnipotent r q : Set (Fixed r q))) (u : naturalUnipotent r q) :
    ∃ v : naturalUnipotent r q,
      pullbackElementary r q p * u.val * (pullbackElementary r q p)⁻¹ = v.val := by
  have hu : unipotentToOriginalFixed r q u ∈ originalUnipotent r q := ⟨u, rfl⟩
  have hc := (Subgroup.mem_normalizer_iff.mp hp (unipotentToOriginalFixed r q u)).mp hu
  obtain ⟨v, hv⟩ := hc
  refine ⟨v, ?_⟩
  have he := congrArg (twistedFixedAction r q) hv
  simp only [map_mul, map_inv, unipotentToOriginalFixed_action] at he
  rw [← pullback_action_eq r q p] at he
  apply upper_conjugate_of_action_eq q r hr (pullbackElementary r q p) u v
  rw [map_mul, map_mul, map_inv]
  exact he.symm

def naturalUpperUnits (q : CFSG.PrimePower) (r : ℕ) : Subgroup (Mat (q.Extension 2) r)ˣ :=
  (naturalUnipotent r q).map (NaturalElementary (q.Extension 2) r).subtype

theorem pullback_normalizer_mem_units_normalizer (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (p : fixedNaturalPullback r q)
    (hp : pullbackSource r q p ∈ Subgroup.normalizer
      (originalUnipotent r q : Set (Fixed r q))) :
    pullbackMatrix r q p ∈ Subgroup.normalizer
      (naturalUpperUnits q r : Set (Mat (q.Extension 2) r)ˣ) := by
  have hforward (t : fixedNaturalPullback r q)
      (ht : pullbackSource r q t ∈ Subgroup.normalizer
        (originalUnipotent r q : Set (Fixed r q))) :
      ∀ x ∈ naturalUpperUnits q r,
        pullbackMatrix r q t * x * (pullbackMatrix r q t)⁻¹ ∈ naturalUpperUnits q r := by
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨v, hv⟩ := pullback_normalizer_conjugate_upper q r hr t ht ⟨a, ha⟩
    refine ⟨v.val, v.property, ?_⟩
    exact congrArg (fun y : NaturalElementary (q.Extension 2) r => y.val) hv.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward p hp x
  · intro hx
    have hpi : pullbackSource r q (p⁻¹) ∈ Subgroup.normalizer
        (originalUnipotent r q : Set (Fixed r q)) := by
      rw [map_inv]
      exact (Subgroup.normalizer _).inv_mem hp
    have h := hforward (p⁻¹) hpi _ hx
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
