import SymmetricSubgroupAsymptotics.RepresentationHeadExact

/-!
# Heads of subrepresentations of an actual representation section

Suppose an ambient representation embeds in a convenient coordinate
representation and maps onto a literal section.  Every subrepresentation
of the section pulls back to the ambient representation.  Its head injects
into the head of that pullback, and the embedding identifies the pullback
with its literal range.  Thus a uniform head bound on subrepresentations of
the coordinate representation descends to every subrepresentation of the
section.

This is deliberately a two-map theorem: the section need not embed back
into the coordinate representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G U V W : Type} [Field k] [Group G]
  [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Pull a character of the target representation back along an actual
intertwiner. -/
def representationHeadPullback
    {rho : Representation k G U} {sigma : Representation k G V}
    (q : rho.IntertwiningMap sigma) :
    sigma.IntertwiningMap (Representation.trivial k G k) →ₗ[k]
      rho.IntertwiningMap (Representation.trivial k G k) where
  toFun f := f.comp q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem representationHeadPullback_injective
    {rho : Representation k G U} {sigma : Representation k G V}
    (q : rho.IntertwiningMap sigma) (hq : Function.Surjective q) :
    Function.Injective (representationHeadPullback q) := by
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := hq v
  exact LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap hfg) u

/-- A surjective representation map cannot increase the head when read
contravariantly. -/
theorem representationHead_finrank_le_of_surjective
    {rho : Representation k G U} {sigma : Representation k G V}
    [FiniteDimensional k U] [FiniteDimensional k V]
    (q : rho.IntertwiningMap sigma) (hq : Function.Surjective q) :
    Module.finrank k
        (sigma.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k
        (rho.IntertwiningMap (Representation.trivial k G k)) :=
  (representationHeadPullback q).finrank_le_finrank_of_injective
    (representationHeadPullback_injective q hq)

/-- Uniform coordinate-representation head bounds descend through an
ambient embedding followed by an unrelated onto section map. -/
theorem sectionSubrepresentation_head_le_of_embedding
    (alpha : Representation k G U)
    (beta : Representation k G V)
    (tau : Representation k G W)
    [FiniteDimensional k U] [FiniteDimensional k V]
    [FiniteDimensional k W]
    (f : alpha.IntertwiningMap beta) (hf : Function.Injective f)
    (q : alpha.IntertwiningMap tau) (hq : Function.Surjective q)
    (cap : ℕ)
    (hbeta : ∀ R : Subrepresentation beta,
      Module.finrank k
        (R.toRepresentation.IntertwiningMap
          (Representation.trivial k G k)) ≤ cap)
    (T : Subrepresentation tau) :
    Module.finrank k
        (T.toRepresentation.IntertwiningMap
          (Representation.trivial k G k)) ≤ cap := by
  let P : Subrepresentation alpha := {
    toSubmodule := T.toSubmodule.comap q.toLinearMap
    apply_mem_toSubmodule := by
      intro g u hu
      change q (alpha g u) ∈ T
      rw [Representation.IntertwiningMap.isIntertwining]
      exact T.apply_mem_toSubmodule g hu }
  let qP : P.toRepresentation.IntertwiningMap T.toRepresentation := {
    toLinearMap := {
      toFun := fun u ↦ ⟨q u.1, u.2⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add q x.1 y.1
      map_smul' := by intro c x; apply Subtype.ext; exact map_smul q c x.1 }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining alpha tau q g u.1 }
  have hqP : Function.Surjective qP := by
    intro t
    obtain ⟨u, hu⟩ := hq t.1
    let uP : P.toSubmodule := ⟨u, by
      change q u ∈ T
      rw [hu]
      exact t.2⟩
    exact ⟨uP, Subtype.ext hu⟩
  let iP : P.toRepresentation.IntertwiningMap alpha := {
    toLinearMap := P.toSubmodule.subtype
    isIntertwining' := by intro g; rfl }
  let fP : P.toRepresentation.IntertwiningMap beta := f.comp iP
  have hfP : Function.Injective fP := hf.comp Subtype.val_injective
  have hrange : Function.Injective
      (RepresentationHeadExact.rangeProjection fP) := by
    intro x y hxy
    exact hfP (congrArg Subtype.val hxy)
  let e : P.toRepresentation.Equiv fP.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection fP).ofBijective
      ⟨hrange, RepresentationHeadExact.rangeProjection_surjective fP⟩
  have hTP := representationHead_finrank_le_of_surjective qP hqP
  have hPR := (RepresentationHeadExact.headEquiv e).finrank_eq
  calc
    _ ≤ _ := hTP
    _ = _ := hPR
    _ ≤ _ := hbeta fP.range

end SymmetricSubgroupAsymptotics

end
