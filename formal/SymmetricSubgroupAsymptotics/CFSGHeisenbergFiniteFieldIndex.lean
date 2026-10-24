import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.GroupTheory.Index

/-! Actual kernel/range counting for a centre-proper subgroup of the
finite-field Heisenberg group. No full-field linearity of its vector
image is required. The resulting orbit bound is valid in every
characteristic; a later symplectic-root realization may require odd
characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIndex

open CFSGHeisenbergCoordinateGroup CFSGHeisenbergFiniteFieldIsotropy
variable {K : Type*} [Field K] {m : ℕ}

def restrictedProjection (H : Subgroup (Element K m)) :
    H →* Multiplicative ((Fin m → K) × (Fin m → K)) := projection.comp H.subtype

theorem restrictedProjection_kernel_card_le [Finite K] (H : Subgroup (Element K m)) :
    Nat.card (restrictedProjection H).ker ≤ Nat.card (centralPreimage H) := by
  let e : (restrictedProjection H).ker → centralPreimage H := fun g =>
    ⟨g.val.val.c, by
      have hg : g.val.val ∈ (projection (K := K) (m := m)).ker := g.property
      obtain ⟨ha, hb⟩ := (mem_projection_ker g.val.val).mp hg
      change central (Multiplicative.ofAdd g.val.val.c) ∈ H
      have he : central (Multiplicative.ofAdd g.val.val.c) = g.val.val :=
        Element.ext ha.symm hb.symm rfl
      rw [he]
      exact g.val.property⟩
  apply Nat.card_le_card_of_injective e
  intro g h he
  have hc : g.val.val.c = h.val.val.c := congrArg Subtype.val he
  have hg : g.val.val ∈ (projection (K := K) (m := m)).ker := g.property
  have hh : h.val.val ∈ (projection (K := K) (m := m)).ker := h.property
  obtain ⟨hga, hgb⟩ := (mem_projection_ker g.val.val).mp hg
  obtain ⟨hha, hhb⟩ := (mem_projection_ker h.val.val).mp hh
  apply Subtype.ext
  apply Subtype.ext
  exact Element.ext (hga.trans hha.symm) (hgb.trans hhb.symm) hc

theorem restrictedProjection_range_card_le [Finite K] (H : Subgroup (Element K m)) :
    Nat.card (restrictedProjection H).range ≤ Nat.card (vectorImage H) := by
  let e : (restrictedProjection H).range → vectorImage H := fun v =>
    ⟨v.val.toAdd, by
      obtain ⟨g, hg⟩ := v.property
      change Multiplicative.ofAdd v.val.toAdd ∈ H.map projection
      exact ⟨g.val, g.property, hg⟩⟩
  apply Nat.card_le_card_of_injective e
  intro v w he
  have hv : v.val.toAdd = w.val.toAdd :=
    congrArg (fun z : vectorImage H => z.val) he
  apply Subtype.ext
  exact Multiplicative.toAdd.injective hv

theorem subgroup_card_le_product [Finite K] (H : Subgroup (Element K m)) :
    Nat.card H ≤ Nat.card (centralPreimage H) * Nat.card (vectorImage H) := by
  have he := (restrictedProjection H).ker.card_mul_index
  rw [Subgroup.index_ker] at he
  calc
    Nat.card H = Nat.card (restrictedProjection H).ker *
        Nat.card (restrictedProjection H).range := he.symm
    _ ≤ Nat.card (centralPreimage H) * Nat.card (vectorImage H) :=
      Nat.mul_le_mul (restrictedProjection_kernel_card_le H)
        (restrictedProjection_range_card_le H)

theorem subgroup_card_mul_prime_le (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (H : Subgroup (Element K m)) (hH : ¬(central (K := K) (m := m)).range ≤ H) :
    p * Nat.card H ≤ Nat.card K ^ (m + 1) := by
  calc
    p * Nat.card H ≤ p * (Nat.card (centralPreimage H) * Nat.card (vectorImage H)) :=
      Nat.mul_le_mul_left p (subgroup_card_le_product H)
    _ = (p * Nat.card (centralPreimage H)) * Nat.card (vectorImage H) :=
      (Nat.mul_assoc _ _ _).symm
    _ ≤ Nat.card K * Nat.card K ^ m :=
      Nat.mul_le_mul
        (proper_additive_card_mul_prime_le p _ (centralPreimage_ne_top H hH))
        (vectorImage_card_le p H hH)
    _ = Nat.card K ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]

theorem index_least (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (H : Subgroup (Element K m)) (hH : ¬(central (K := K) (m := m)).range ≤ H) :
    p * Nat.card K ^ m ≤ H.index := by
  have hq : 0 < Nat.card K := Nat.card_pos
  have hs := subgroup_card_mul_prime_le p H hH
  have he := H.card_mul_index
  rw [card] at he
  apply Nat.le_of_mul_le_mul_left _ (pow_pos hq (m + 1))
  calc
    Nat.card K ^ (m + 1) * (p * Nat.card K ^ m) =
        p * Nat.card K ^ (2 * m + 1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (Nat.card K ^ (m + 1)) p,
        Nat.mul_assoc, ← pow_add]
      rw [show m + 1 + m = 2 * m + 1 by omega]
    _ = (p * Nat.card H) * H.index := by rw [← he, Nat.mul_assoc]
    _ ≤ Nat.card K ^ (m + 1) * H.index := Nat.mul_le_mul_right H.index hs

theorem degree_le_of_central_motion (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    {X : Type*} [Finite X] [MulAction (Element K m) X]
    (x : X) (c : Multiplicative K) (hc : central (m := m) c • x ≠ x) :
    p * Nat.card K ^ m ≤ Nat.card X := by
  have hH : ¬(central (K := K) (m := m)).range ≤
      MulAction.stabilizer (Element K m) x := by
    intro hh
    exact hc (hh ⟨c, rfl⟩)
  calc
    p * Nat.card K ^ m ≤ (MulAction.stabilizer (Element K m) x).index := index_least p _ hH
    _ = (MulAction.orbit (Element K m) x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

end SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIndex
