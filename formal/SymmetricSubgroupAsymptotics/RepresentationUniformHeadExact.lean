import SymmetricSubgroupAsymptotics.RepresentationHeadExact

/-! Uniform heads are subadditive in an actual exact representation sequence.
For a correlated middle subrepresentation, pull back the first term and
retain the image in the last term. This isolates the linear algebra from
the carrier-heavy coinduced application. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepresentationUniformHeadExact

variable {k G U V W : Type} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  (alpha : Representation k G U) (beta : Representation k G V)
  (gamma : Representation k G W)
  (i : alpha.IntertwiningMap beta) (q : beta.IntertwiningMap gamma)

def pullback (B : Subrepresentation beta) : Subrepresentation alpha where
  toSubmodule := B.toSubmodule.comap i.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change i (alpha g v) ∈ B
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hv

def restrictedInclusion (B : Subrepresentation beta) :
    (pullback alpha beta i B).toRepresentation.IntertwiningMap B.toRepresentation where
  toLinearMap := {
    toFun v := ⟨i v.1, v.2⟩
    map_add' v w := Subtype.ext (map_add i v.1 w.1)
    map_smul' c v := Subtype.ext (map_smul i c v.1) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ i g v.1

def restrictedMap (B : Subrepresentation beta) :
    B.toRepresentation.IntertwiningMap gamma where
  toLinearMap := q.toLinearMap.comp B.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact Representation.IntertwiningMap.isIntertwining _ _ q g v.1

theorem restricted_exact
    (hexact : i.toLinearMap.range = q.toLinearMap.ker)
    (B : Subrepresentation beta) :
    (restrictedInclusion alpha beta i B).toLinearMap.range =
      (RepresentationHeadExact.rangeProjection
        (k := k) (G := G) (V := B.toSubmodule) (W := W)
        (ρ := B.toRepresentation) (σ := gamma)
        (restrictedMap beta gamma q B)).toLinearMap.ker := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    apply Subtype.ext
    have hi : i.toLinearMap v.1 ∈ q.toLinearMap.ker := by
      rw [← hexact]
      exact ⟨v.1, rfl⟩
    exact hi
  · intro b hb
    have hq : q.toLinearMap b.1 = 0 :=
      congrArg (fun v : (restrictedMap beta gamma q B).range.toSubmodule => (v : W)) hb
    have hrange : b.1 ∈ i.toLinearMap.range := by
      rw [hexact]
      exact hq
    obtain ⟨a, ha⟩ := hrange
    have haB : a ∈ pullback alpha beta i B := by
      change i.toLinearMap a ∈ B
      rw [ha]
      exact b.2
    exact ⟨⟨a, haB⟩, Subtype.ext ha⟩

include i q in
/-- Uniform head bounds on the two outer representations bound every
subrepresentation of the middle one. -/
theorem uniform_head_le_add
    [FiniteDimensional k U] [FiniteDimensional k V] [FiniteDimensional k W]
    (hexact : i.toLinearMap.range = q.toLinearMap.ker)
    (a b : ℕ)
    (ha : ∀ A : Subrepresentation alpha,
      Module.finrank k
        (A.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ a)
    (hb : ∀ C : Subrepresentation gamma,
      Module.finrank k
        (C.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ b)
    (B : Subrepresentation beta) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ a + b := by
  let A := pullback alpha beta i B
  let r : B.toRepresentation.IntertwiningMap gamma := restrictedMap beta gamma q B
  letI : FiniteDimensional k A.toSubmodule :=
    FiniteDimensional.of_injective A.toSubmodule.subtype A.toSubmodule.subtype_injective
  letI : FiniteDimensional k B.toSubmodule :=
    FiniteDimensional.of_injective B.toSubmodule.subtype B.toSubmodule.subtype_injective
  letI : FiniteDimensional k r.range.toSubmodule :=
    FiniteDimensional.of_injective r.range.toSubmodule.subtype r.range.toSubmodule.subtype_injective
  have h := RepresentationHeadExact.head_finrank_le_of_range_eq_ker
    (k := k) (G := G) (V := B.toSubmodule) (W := A.toSubmodule)
    (Z := r.range.toSubmodule) (ρ := B.toRepresentation)
    (σ := A.toRepresentation) (τ := r.range.toRepresentation)
    (restrictedInclusion alpha beta i B)
    (RepresentationHeadExact.rangeProjection r)
    (RepresentationHeadExact.rangeProjection_surjective r)
    (restricted_exact alpha beta gamma i q hexact B)
  exact h.trans (Nat.add_le_add (ha A) (hb r.range))

end SymmetricSubgroupAsymptotics.RepresentationUniformHeadExact

end
