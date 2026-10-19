import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualSectionHead
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetFixedHead

/-! The fixed projector uses the same binary subspace and original
surjective section map as the active projector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualFixedHead
open BinaryTwistedQuartetPolynomial (Bit)
open BinaryTwistedQuartetLoewyCoordinates

variable {H : Type} [Group H] (rho : Representation Bit H Space)
    (a : H) (ha : ∀ v, rho a v=cycleAction v)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (sigma : Representation Bit H Q)

include ha in
theorem subspace_fixed (W : Subrepresentation rho)
    (q : Representation.IntertwiningMap W.toRepresentation sigma)
    (hq : Function.Surjective q) (hcube : (sigma a)^3=1) :
    Module.finrank Bit (LinearMap.range (1+sigma a+(sigma a)^2))≤2 := by
  have hc : ∀ v, v∈W → cycleAction v∈W := by
    intro v hv
    rw [← ha]
    exact W.apply_mem_toSubmodule a hv
  apply BinaryTwistedQuartetFixedHead.fixed_rank_le_two W.toSubmodule hc
    q.toLinearMap hq (sigma a) hcube
  intro v
  have he : W.toRepresentation a v=⟨cycleAction v,hc v v.property⟩ := Subtype.ext (ha v)
  rw [← he]
  exact Representation.IntertwiningMap.isIntertwining _ _ q a v

include ha in
theorem section_fixed {V : Type} [AddCommGroup V] [Module Bit V]
    (alpha : Representation Bit H V)
    (j : Representation.IntertwiningMap alpha rho) (hj : Function.Injective j)
    (q : Representation.IntertwiningMap alpha sigma) (hq : Function.Surjective q)
    (hcube : (sigma a)^3=1) :
    Module.finrank Bit (LinearMap.range (1+sigma a+(sigma a)^2))≤2 := by
  have hr : Function.Injective (RepresentationHeadExact.rangeProjection j) := by
    intro x y h
    exact hj (congrArg Subtype.val h)
  let e : alpha.Equiv j.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection j).ofBijective
      ⟨hr,RepresentationHeadExact.rangeProjection_surjective j⟩
  let qR := q.comp e.symm.toIntertwiningMap
  exact subspace_fixed rho a ha sigma j.range qR (hq.comp e.symm.surjective) hcube

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualFixedHead
