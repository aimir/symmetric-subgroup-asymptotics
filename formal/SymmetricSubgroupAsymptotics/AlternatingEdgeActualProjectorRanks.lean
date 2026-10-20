import SymmetricSubgroupAsymptotics.AlternatingEdgeActualSectionHead
import SymmetricSubgroupAsymptotics.IntertwiningProjectorRank
import SymmetricSubgroupAsymptotics.SurjectiveProjectorRank

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeActualProjectorRanks
open AlternatingEdgeBinaryProjectors

variable {H : Type} [Group H] (beta : Representation (ZMod 2) H Vector)
    (a : H) (ha : ∀ v, beta a v=A v)
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [FiniteDimensional (ZMod 2) Q] (sigma : Representation (ZMod 2) H Q)

include ha in
theorem subspace_ranks (W : Subrepresentation beta)
    (q : Representation.IntertwiningMap W.toRepresentation sigma)
    (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) (LinearMap.range (1+sigma a+(sigma a)^2)) ≤ 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range (sigma a+(sigma a)^2)) ≤ 4 := by
  let T := W.toRepresentation a
  have hj (v : W) : (T v : Vector)=A v := ha v
  have hqT (v : W) : q (T v)=sigma a (q v) :=
    Representation.IntertwiningMap.isIntertwining _ _ q a v
  constructor
  · have hi := IntertwiningProjectorRank.rank_le W.toSubmodule.subtype
      Subtype.val_injective (1+T+T^2) fixed (by
        intro v
        change v.val + (T v).val + (T (T v)).val = v.val + A v + A (A v)
        rw [hj,hj,hj])
    have hs := SurjectiveProjectorRank.rank_le q.toLinearMap hq
      (1+T+T^2) (1+sigma a+(sigma a)^2) (by
        intro v
        change q (v+T v+T (T v)) = q v+sigma a (q v)+sigma a (sigma a (q v))
        rw [map_add,map_add,hqT,hqT,hqT])
    exact hs.trans (hi.trans fixed_rank_le_two)
  · have hi := IntertwiningProjectorRank.rank_le W.toSubmodule.subtype
      Subtype.val_injective (T+T^2) active (by
        intro v
        change (T v).val + (T (T v)).val = A v + A (A v)
        rw [hj,hj,hj])
    have hs := SurjectiveProjectorRank.rank_le q.toLinearMap hq
      (T+T^2) (sigma a+(sigma a)^2) (by
        intro v
        change q (T v+T (T v)) = sigma a (q v)+sigma a (sigma a (q v))
        rw [map_add,hqT,hqT,hqT])
    exact hs.trans (hi.trans active_rank_le_four)

include ha in
theorem section_ranks {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (alpha : Representation (ZMod 2) H V)
    (j : Representation.IntertwiningMap alpha beta) (hj : Function.Injective j)
    (q : Representation.IntertwiningMap alpha sigma) (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) (LinearMap.range (1+sigma a+(sigma a)^2)) ≤ 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range (sigma a+(sigma a)^2)) ≤ 4 := by
  have hr : Function.Injective (RepresentationHeadExact.rangeProjection j) := by
    intro x y h
    exact hj (congrArg Subtype.val h)
  let e : alpha.Equiv j.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection j).ofBijective
      ⟨hr,RepresentationHeadExact.rangeProjection_surjective j⟩
  exact subspace_ranks beta a ha sigma j.range (q.comp e.symm.toIntertwiningMap)
    (hq.comp e.symm.surjective)

end SymmetricSubgroupAsymptotics.AlternatingEdgeActualProjectorRanks
