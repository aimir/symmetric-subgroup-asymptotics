import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index

/-! The two quantitative simple-index conclusions use literal subgroup indices
and the literal quotient of automorphisms by inner automorphisms. This file
transports those objects along actual group isomorphisms, so concrete-family
proofs can be reused without postulating numerical labels for abstract groups. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

private theorem map_ne_top {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (K : Subgroup G) (hK : K ≠ ⊤) :
    K.map e.toMonoidHom ≠ ⊤ := by
  intro he
  apply hK
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [he, Subgroup.map_top_of_surjective _ e.surjective]

theorem leastProperIndex_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (ell : ℕ) (h : LeastProperIndex G ell) :
    LeastProperIndex H ell := by
  obtain ⟨⟨K, hK, hk⟩, hmin⟩ := h
  refine ⟨⟨K.map e.toMonoidHom, map_ne_top e K hK, ?_⟩, ?_⟩
  · exact (K.index_map_equiv e).trans hk
  · intro L hL
    have hle := hmin (L.map e.symm.toMonoidHom) (map_ne_top e.symm L hL)
    exact hle.trans_eq (L.index_map_equiv e.symm)

theorem leastProperIndex_congr {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (ell : ℕ) :
    LeastProperIndex G ell ↔ LeastProperIndex H ell :=
  ⟨leastProperIndex_of_mulEquiv e ell, leastProperIndex_of_mulEquiv e.symm ell⟩

/-- Automorphism conjugation sends precisely the inner automorphisms to the
inner automorphisms, not merely to an overgroup of them. -/
theorem map_inner_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    (Inner G).map (MulAut.congr e).toMonoidHom = Inner H := by
  ext a
  constructor
  · rintro ⟨f, ⟨g, rfl⟩, rfl⟩
    refine ⟨e g, ?_⟩
    apply MulEquiv.ext
    intro x
    simp [MulAut.congr, MulAut.conj_apply, map_mul, map_inv]
  · rintro ⟨h, rfl⟩
    refine ⟨MulAut.conj (e.symm h), ⟨e.symm h, rfl⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    simp [MulAut.congr, MulAut.conj_apply, map_mul, map_inv]

/-- The actual outer-automorphism groups are isomorphic. -/
noncomputable def outerCongr {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Outer G ≃* Outer H :=
  QuotientGroup.congr (Inner G) (Inner H) (MulAut.congr e) (map_inner_congr e)

theorem outer_card_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (outerCongr e).toEquiv

/-- The exact two numerical conclusions are transported together. -/
theorem simpleIndexBounds_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H)
    (hH : ∀ ell : ℕ, LeastProperIndex H ell →
      ell ^ 2 < Nat.card H ∧ (Nat.card (Outer H) : ℝ) ≤ 3 * Real.logb 2 ell) :
    ∀ ell : ℕ, LeastProperIndex G ell →
      ell ^ 2 < Nat.card G ∧ (Nat.card (Outer G) : ℝ) ≤ 3 * Real.logb 2 ell := by
  intro ell hell
  have h := hH ell (leastProperIndex_of_mulEquiv e ell hell)
  simpa only [Nat.card_congr e.toEquiv, outer_card_congr e] using h

/-- Reducing this published input to CFSG leaves only concrete-family
inequalities. Those inequalities are not supplied by classification itself. -/
theorem publishedSimpleIndexBounds_of_models (hCFSG : CFSG.CFSGClassification)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → ∀ ell : ℕ, LeastProperIndex i.Model ell →
        ell ^ 2 < Nat.card i.Model ∧
          (Nat.card (Outer i.Model) : ℝ) ≤ 3 * Real.logb 2 ell) :
    PublishedSimpleIndexBounds := by
  intro G _ _ _ hG
  exact of_nonabelian_simple_models hCFSG
    (fun H => ∀ ell : ℕ, LeastProperIndex H ell →
      ell ^ 2 < Nat.card H ∧ (Nat.card (Outer H) : ℝ) ≤ 3 * Real.logb 2 ell)
    (fun e => simpleIndexBounds_of_mulEquiv e) models G hG

end SymmetricSubgroupAsymptotics.CFSGReduction
