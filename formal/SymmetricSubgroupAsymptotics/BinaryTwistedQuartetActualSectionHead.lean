import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetCoinvariantHead
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetTrivialHead
import SymmetricSubgroupAsymptotics.RepresentationHeadExact

/-! The literal head certificates apply to actual acting elements and
the SAME binary subspaces. An injective original kernel chart followed
by its unrelated original quotient map is kept as a two-map section. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualSectionHead
open BinaryTwistedQuartetPolynomial (Bit)
open BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetLoewyAugmentations

variable {H : Type} [Group H] (rho : Representation Bit H Space)
    (a t s : H) (ha : ∀ v, rho a v=cycleAction v)
    (ht : ∀ v, rho t v=flipAction v) (hs : ∀ v, rho s v=secondFlip v)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (sigma : Representation Bit H Q)

include ha ht hs in
theorem subspace_nontrivial (W : Subrepresentation rho)
    (q : Representation.IntertwiningMap W.toRepresentation sigma)
    (hq : Function.Surjective q) (hqt : sigma t=1) (hqs : sigma s=1) :
    Module.finrank Bit (LinearMap.range (sigma a+(sigma a)^2))≤2 := by
  have hc : ∀ v, v∈W → cycleAction v∈W := by
    intro v hv
    rw [← ha]
    exact W.apply_mem_toSubmodule a hv
  have hf : ∀ v, v∈W → flipAction v∈W := by
    intro v hv
    rw [← ht]
    exact W.apply_mem_toSubmodule t hv
  have hsecond : ∀ v, v∈W → secondFlip v∈W := by
    intro v hv
    rw [← hs]
    exact W.apply_mem_toSubmodule s hv
  apply BinaryTwistedQuartetCoinvariantHead.nontrivial_rank_le_two W.toSubmodule
    hc hf hsecond q.toLinearMap hq (sigma a)
  · intro v
    have he : W.toRepresentation a v=⟨cycleAction v,hc v v.property⟩ := Subtype.ext (ha v)
    rw [← he]
    exact Representation.IntertwiningMap.isIntertwining _ _ q a v
  · intro v
    have he : W.toRepresentation t v=⟨flipAction v,hf v v.property⟩ := Subtype.ext (ht v)
    rw [← he]
    change q (W.toRepresentation t v)=q v
    rw [Representation.IntertwiningMap.isIntertwining _ _ q t v,hqt]
    rfl
  · intro v
    have he : W.toRepresentation s v=⟨secondFlip v,hsecond v v.property⟩ := Subtype.ext (hs v)
    rw [← he]
    change q (W.toRepresentation s v)=q v
    rw [Representation.IntertwiningMap.isIntertwining _ _ q s v,hqs]
    rfl

include ha in
theorem subspace_trivial (W : Subrepresentation rho)
    (q : Representation.IntertwiningMap W.toRepresentation sigma)
    (hq : Function.Surjective q) (hqa : sigma a=1) : Module.finrank Bit Q≤2 := by
  have hc : ∀ v, v∈W → cycleAction v∈W := by
    intro v hv
    rw [← ha]
    exact W.apply_mem_toSubmodule a hv
  apply BinaryTwistedQuartetTrivialHead.rank_le_two W.toSubmodule hc q.toLinearMap hq
  intro v
  have he : W.toRepresentation a v=⟨cycleAction v,hc v v.property⟩ := Subtype.ext (ha v)
  rw [← he]
  change q (W.toRepresentation a v)=q v
  rw [Representation.IntertwiningMap.isIntertwining _ _ q a v,hqa]
  rfl

variable {V : Type} [AddCommGroup V] [Module Bit V]

include ha ht hs in
/-- No inverse embedding of the original section into the ambient
coordinate representation is assumed. -/
theorem section_nontrivial (alpha : Representation Bit H V)
    (j : Representation.IntertwiningMap alpha rho) (hj : Function.Injective j)
    (q : Representation.IntertwiningMap alpha sigma) (hq : Function.Surjective q)
    (hqt : sigma t=1) (hqs : sigma s=1) :
    Module.finrank Bit (LinearMap.range (sigma a+(sigma a)^2))≤2 := by
  have hr : Function.Injective (RepresentationHeadExact.rangeProjection j) := by
    intro x y h
    exact hj (congrArg Subtype.val h)
  let e : alpha.Equiv j.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection j).ofBijective
      ⟨hr,RepresentationHeadExact.rangeProjection_surjective j⟩
  let qR := q.comp e.symm.toIntertwiningMap
  exact subspace_nontrivial rho a t s ha ht hs sigma j.range qR
    (hq.comp e.symm.surjective) hqt hqs

include ha in
theorem section_trivial (alpha : Representation Bit H V)
    (j : Representation.IntertwiningMap alpha rho) (hj : Function.Injective j)
    (q : Representation.IntertwiningMap alpha sigma) (hq : Function.Surjective q)
    (hqa : sigma a=1) : Module.finrank Bit Q≤2 := by
  have hr : Function.Injective (RepresentationHeadExact.rangeProjection j) := by
    intro x y h
    exact hj (congrArg Subtype.val h)
  let e : alpha.Equiv j.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection j).ofBijective
      ⟨hr,RepresentationHeadExact.rangeProjection_surjective j⟩
  let qR := q.comp e.symm.toIntertwiningMap
  exact subspace_trivial rho a ha sigma j.range qR (hq.comp e.symm.surjective) hqa

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualSectionHead
