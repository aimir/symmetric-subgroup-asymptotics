import SymmetricSubgroupAsymptotics.External.CFSG.Classification
import SymmetricSubgroupAsymptotics.SemisimpleNormalChart

/-!
# Transport from the pinned concrete CFSG models

The exhaustiveness statement supplies an actual group isomorphism. Finiteness,
simplicity and noncommutativity of the source are transported to the selected
model, rather than assumed for every model in the index. Thus applications do
not have to reprove the converse direction of classification.

This file proves transport and elimination principles only. Its model-property
arguments remain genuine proof obligations; no generation, order, automorphism,
or subgroup-index theorem is included in the classification hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

/-- A concrete model and an actual isomorphism, in any universe. -/
structure SimpleModelWitness (G : Type*) [Group G] where
  index : CFSG.Index
  equiv : G ≃* index.Model

/-- The single Type-0 classification hypothesis provides witnesses in all universes. -/
noncomputable def simpleModelWitness (hCFSG : CFSG.CFSGClassification)
    (G : Type*) [Group G] [Finite G] [IsSimpleGroup G] : SimpleModelWitness G := by
  exact ⟨Classical.choose (hCFSG.classify G),
    Classical.choice (Classical.choose_spec (hCFSG.classify G))⟩

namespace SimpleModelWitness

theorem finite_model {G : Type*} [Group G] [Finite G]
    (W : SimpleModelWitness G) : Finite W.index.Model :=
  Finite.of_equiv G W.equiv.toEquiv

theorem simple_model {G : Type*} [Group G] [IsSimpleGroup G]
    (W : SimpleModelWitness G) : IsSimpleGroup W.index.Model :=
  W.equiv.symm.isSimpleGroup

end SimpleModelWitness

/-- Commutativity is transported along the literal group isomorphism. -/
theorem isMulCommutative_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : IsMulCommutative G ↔ IsMulCommutative H := by
  constructor
  · intro h
    apply isMulCommutative_iff.mpr
    intro x y
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e ((isMulCommutative_iff.mp h) a b)
  · intro h
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    simpa only [map_mul] using (isMulCommutative_iff.mp h) (e x) (e y)

/-- The project's exact centerlessness predicate is invariant under isomorphism. -/
theorem isCenterless_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : IsCenterless G ↔ IsCenterless H := by
  constructor
  · intro h x hx
    have hc : ∀ y : G, e.symm x * y = y * e.symm x := by
      intro y
      apply e.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using hx (e y)
    have hh := congrArg e (h (e.symm x) hc)
    simpa only [MulEquiv.apply_symm_apply, map_one] using hh
  · intro h x hx
    have hc : ∀ y : H, e x * y = y * e x := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (hx z)
    apply e.injective
    simpa only [map_one] using h (e x) hc

/-- A transported nonabelian simple group cannot land in a cyclic branch. -/
theorem SimpleModelWitness.not_cyclic {G : Type*} [Group G]
    (W : SimpleModelWitness G) (hG : ¬ IsMulCommutative G)
    (p : ℕ) (hp : p.Prime) : W.index ≠ CFSG.Index.cyclic p hp := by
  intro hi
  have hc : IsMulCommutative W.index.Model := by
    rw [hi]
    change IsMulCommutative (Multiplicative (ZMod p))
    infer_instance
  exact hG ((isMulCommutative_congr W.equiv).mpr hc)

/-- A property transported by isomorphism follows from its concrete simple-model
cases. The model cases may use finiteness and simplicity transported from the
source; global finiteness or simplicity of every indexed construction is not needed. -/
theorem of_simple_models (hCFSG : CFSG.CFSGClassification)
    (P : (G : Type) → [Group G] → Prop)
    (transport : ∀ {G H : Type} [Group G] [Group H], (G ≃* H) → P H → P G)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model], P i.Model)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] : P G := by
  let W := simpleModelWitness hCFSG G
  letI := W.finite_model
  letI := W.simple_model
  exact transport W.equiv (models W.index)

/-- The nonabelian specialization exposes exactly the family-level obligations. -/
theorem of_nonabelian_simple_models (hCFSG : CFSG.CFSGClassification)
    (P : (G : Type) → [Group G] → Prop)
    (transport : ∀ {G H : Type} [Group G] [Group H], (G ≃* H) → P H → P G)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → P i.Model)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) : P G := by
  let W := simpleModelWitness hCFSG G
  letI := W.finite_model
  letI := W.simple_model
  have hn : ¬ IsMulCommutative W.index.Model := by
    intro hm
    exact hG ((isMulCommutative_congr W.equiv).mpr hm)
  exact transport W.equiv (models W.index hn)

end SymmetricSubgroupAsymptotics.CFSGReduction
