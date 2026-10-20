import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Supplement-preserving generators for the large-orbit argument

Ordinary generation of a soluble extension needs more than a normal-closure
bound for its kernel.  The property below retains exactly what is needed:
one tuple supplements every subgroup which already supplements the given
normal subgroup.  For an abelian normal subgroup, ambient normal generators
have this property.  This file contains group-theoretic lifting only; it
asserts no new published generator estimate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences

variable {G Q : Type} [Group G] [Group Q]

/-- The same tuple supplements every supplement of `N`.  Its entries belong
to the original subgroup and its closure is taken in the original group. -/
def SupplementTuple (N : Subgroup G) (n : ℕ) : Prop :=
  ∃ x : Fin n → G, Set.range x ⊆ N ∧
    ∀ H : Subgroup G, H ⊔ N = ⊤ →
      H ⊔ Subgroup.closure (Set.range x) = ⊤

/-- Ambient normal generators of an abelian normal subgroup preserve
ordinary generation in every extension by that subgroup. -/
theorem sup_closure_eq_top_of_abelian_normalClosure
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    {n : ℕ} (x : Fin n → G)
    (hxN : Set.range x ⊆ N)
    (hx : Subgroup.normalClosure (Set.range x) = N)
    (H : Subgroup G) (hHN : H ⊔ N = ⊤) :
    H ⊔ Subgroup.closure (Set.range x) = ⊤ := by
  let K : Subgroup G := H ⊔ Subgroup.closure (Set.range x)
  have hconj : Group.conjugatesOfSet (Set.range x) ⊆ K := by
    intro z hz
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hg : g ∈ H ⊔ N := by rw [hHN]; trivial
    obtain ⟨h, hh, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hba : b * a = a * b := by
      exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : N) ⟨a, hxN ha⟩)
    have heq : (h * b) * a * (h * b)⁻¹ = h * a * h⁻¹ := by
      calc
        (h * b) * a * (h * b)⁻¹ = h * (b * a * b⁻¹) * h⁻¹ := by group
        _ = h * a * h⁻¹ := by rw [hba, mul_inv_cancel_right]
    rw [heq]
    exact K.mul_mem (K.mul_mem (show h ∈ K from Subgroup.mem_sup_left hh)
      (show a ∈ K from Subgroup.mem_sup_right (Subgroup.subset_closure ha)))
      (K.inv_mem (show h ∈ K from Subgroup.mem_sup_left hh))
  have hNK : N ≤ K := by
    rw [← hx]
    exact (Subgroup.closure_le _).mpr hconj
  apply top_unique
  rw [← hHN]
  exact sup_le (show H ≤ K from le_sup_left) hNK

/-- The fixed-witness supplement lemma packaged as an existential tuple. -/
theorem supplementTuple_of_abelian_normalClosure
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    {n : ℕ} (x : Fin n → G)
    (hxN : Set.range x ⊆ N)
    (hx : Subgroup.normalClosure (Set.range x) = N) :
    SupplementTuple N n :=
  ⟨x, hxN, fun H hHN =>
    sup_closure_eq_top_of_abelian_normalClosure N x hxN hx H hHN⟩

/-- A tuple for the full group, with the supplement property, is an
ordinary generating tuple.  No nilpotence assumption is needed. -/
theorem closure_eq_top_of_supplementTuple
    {n : ℕ} (h : SupplementTuple (⊤ : Subgroup G) n) :
    ∃ x : Fin n → G, Subgroup.closure (Set.range x) = ⊤ := by
  obtain ⟨x, hxN, hx⟩ := h
  exact ⟨x, by simpa using hx ⊥ (by simp)⟩

/-- The supplement property can be checked after a surjective map whose
kernel is already contained in the subgroup being supplemented. -/
theorem sup_eq_top_of_map_eq_top
    (f : G →* Q) (_hf : Function.Surjective f)
    (H N : Subgroup G) (hker : f.ker ≤ N)
    (hmap : (H ⊔ N).map f = ⊤) : H ⊔ N = ⊤ := by
  apply top_unique
  intro g _
  have hg : f g ∈ (H ⊔ N).map f := by rw [hmap]; trivial
  obtain ⟨a, ha, hag⟩ := hg
  have hdiff : a⁻¹ * g ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
  have hd : a⁻¹ * g ∈ H ⊔ N := Subgroup.mem_sup_right (hker hdiff)
  simpa only [mul_inv_cancel_left] using (H ⊔ N).mul_mem ha hd

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
