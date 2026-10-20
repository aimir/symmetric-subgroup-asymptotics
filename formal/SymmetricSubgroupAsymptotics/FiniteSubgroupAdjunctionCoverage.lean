import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Set
import Mathlib.Order.Atoms.Finite

/-!
# Conjugacy coverage from finite subgroup adjunctions

A finite list is exhaustive up to conjugacy if it contains the trivial
subgroup and adjoining any one ambient element to any listed subgroup
produces a conjugate of another listed subgroup.  The local transitions
are exact subgroup equalities; completeness is proved below, rather than
supplied as a certificate field.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

variable {G I : Type*} [Group G] (rows : I → Subgroup G)

/-- The conjugator belongs to the actual ambient group. -/
def Covered (U : Subgroup G) : Prop :=
  ∃ i : I, ∃ c : G, MulAut.conj c • U = rows i

/-- Only the listed rows need local adjunction checks: conjugating both
the old subgroup and the adjoined element transports the general step. -/
theorem covered_adjoin
    (hstep : ∀ i : I, ∀ g : G, ∃ j : I, ∃ c : G,
      MulAut.conj c • (rows i ⊔ Subgroup.closure {g}) = rows j)
    {U : Subgroup G} (hU : Covered rows U) (g : G) :
    Covered rows (U ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, c, hc⟩ := hU
  obtain ⟨j, d, hd⟩ := hstep i ((MulAut.conj c) g)
  refine ⟨j, d * c, ?_⟩
  calc
    MulAut.conj (d * c) • (U ⊔ Subgroup.closure {g}) =
        MulAut.conj d • (MulAut.conj c • (U ⊔ Subgroup.closure {g})) := by
      rw [map_mul, mul_smul]
    _ = MulAut.conj d • (rows i ⊔
        Subgroup.closure {((MulAut.conj c) g)}) := by
      rw [Subgroup.smul_sup, hc, Subgroup.smul_closure, Set.smul_set_singleton]
      rfl
    _ = rows j := hd

/-- Local, bounded adjunction checks establish coverage of every actual
subgroup.  The proof chooses a maximal covered subgroup inside the target;
any missing element would give a strictly larger covered subgroup. -/
theorem complete [Finite G]
    (hbot : ∃ i : I, rows i = ⊥)
    (hstep : ∀ i : I, ∀ g : G, ∃ j : I, ∃ c : G,
      MulAut.conj c • (rows i ⊔ Subgroup.closure {g}) = rows j)
    (U : Subgroup G) : Covered rows U := by
  classical
  letI : Finite (Subgroup G) := Finite.of_injective
    (fun V : Subgroup G => (V : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {V | Covered rows V ∧ V ≤ U}
  have hb : (⊥ : Subgroup G) ∈ S := by
    obtain ⟨i, hi⟩ := hbot
    exact ⟨⟨i, 1, by simpa only [Subgroup.smul_bot] using hi.symm⟩, bot_le⟩
  obtain ⟨V, _, hmax⟩ := (Set.toFinite S).exists_le_maximal hb
  have hV : Covered rows V := hmax.1.1
  have hVU : V ≤ U := hmax.1.2
  by_cases heq : V = U
  · exact heq ▸ hV
  · have hnot : ¬ U ≤ V := fun h => heq (le_antisymm hVU h)
    obtain ⟨g, hgU, hgnV⟩ := Set.not_subset.mp hnot
    let W : Subgroup G := V ⊔ Subgroup.closure {g}
    have hW : Covered rows W := covered_adjoin rows hstep hV g
    have hWU : W ≤ U := sup_le hVU ((Subgroup.closure_le U).mpr (by
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hgU))
    have hWV : W ≤ V := hmax.2 ⟨hW, hWU⟩ le_sup_left
    have hgW : g ∈ W :=
      (show Subgroup.closure {g} ≤ W from le_sup_right)
        (Subgroup.subset_closure (by simp))
    exact False.elim (hgnV (hWV hgW))

end SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

end
