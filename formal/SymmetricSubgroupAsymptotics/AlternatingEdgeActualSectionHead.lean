import SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryCoinvariantRank
import SymmetricSubgroupAsymptotics.RepresentationHeadExact

/-! The edge coinvariant bound on an actual embedded section with its
original surjective quotient map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeActualSectionHead
open AlternatingEdgeBinaryProjectors

variable {H : Type} [Group H] (beta : Representation (ZMod 2) H Vector)
    (a : H) (t : Fin 3 → H)
    (ha : ∀ v, beta a v = A v)
    (ht : ∀ d v, beta (t d) v = rho (klein d) v)
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [FiniteDimensional (ZMod 2) Q] (sigma : Representation (ZMod 2) H Q)

include ha ht in
theorem subspace_active (W : Subrepresentation beta)
    (q : Representation.IntertwiningMap W.toRepresentation sigma)
    (hq : Function.Surjective q) (hqt : ∀ d, sigma (t d)=1) :
    Module.finrank (ZMod 2) (LinearMap.range (sigma a+(sigma a)^2)) ≤ 2 := by
  have hA : ∀ v ∈ W, A v ∈ W := by
    intro v hv
    rw [← ha]
    exact W.apply_mem_toSubmodule a hv
  have hD : ∀ d v, v ∈ W → difference d v ∈ W := by
    intro d v hv
    change v + rho (klein d) v ∈ W
    rw [← ht]
    exact W.toSubmodule.add_mem hv (W.apply_mem_toSubmodule (t d) hv)
  apply quotient_active_rank_le_two W.toSubmodule hA hD q.toLinearMap hq (sigma a)
  · intro v
    have he : W.toRepresentation a v=⟨A v,hA v v.property⟩ := Subtype.ext (ha v)
    rw [← he]
    exact Representation.IntertwiningMap.isIntertwining _ _ q a v
  · intro d v
    have he : (⟨difference d v,hD d v v.property⟩ : W) =
        v + W.toRepresentation (t d) v := by
      apply Subtype.ext
      change v.val + rho (klein d) v = v.val + beta (t d) v
      rw [ht]
    rw [he,map_add]
    change q v + q (W.toRepresentation (t d) v) = 0
    rw [Representation.IntertwiningMap.isIntertwining _ _ q (t d) v,hqt]
    change q v + q v = 0
    simpa only [← two_smul (ZMod 2) (q v), show (2 : ZMod 2)=0 from rfl, zero_smul]

include ha ht in
theorem section_active {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (alpha : Representation (ZMod 2) H V)
    (j : Representation.IntertwiningMap alpha beta) (hj : Function.Injective j)
    (q : Representation.IntertwiningMap alpha sigma) (hq : Function.Surjective q)
    (hqt : ∀ d, sigma (t d)=1) :
    Module.finrank (ZMod 2) (LinearMap.range (sigma a+(sigma a)^2)) ≤ 2 := by
  have hr : Function.Injective (RepresentationHeadExact.rangeProjection j) := by
    intro x y h
    exact hj (congrArg Subtype.val h)
  let e : alpha.Equiv j.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection j).ofBijective
      ⟨hr,RepresentationHeadExact.rangeProjection_surjective j⟩
  let qR := q.comp e.symm.toIntertwiningMap
  exact subspace_active beta a t ha ht sigma j.range qR
    (hq.comp e.symm.surjective) hqt

end SymmetricSubgroupAsymptotics.AlternatingEdgeActualSectionHead
