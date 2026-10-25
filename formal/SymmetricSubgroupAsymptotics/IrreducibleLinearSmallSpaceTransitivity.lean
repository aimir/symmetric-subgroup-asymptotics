import SymmetricSubgroupAsymptotics.IrreducibleLinearInvariantSmallSet
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Card

/-! Two distinct nonzero orbits of an irreducible linear action both have
more elements than the dimension. Thus a space with at most twice the
dimension plus two elements has only one nonzero orbit. In particular
this applies to a binary space of dimension three and cardinal eight. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IrreducibleLinearSmallSpaceTransitivity

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]
    [Finite V] [FiniteDimensional K V]

theorem exists_map_eq_of_nonzero
    (ρ : G →* (V ≃ₗ[K] V))
    (hirr : ∀ W : Submodule K V,
      (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdim : 1 < Module.finrank K V)
    (hcard : Nat.card V ≤ 2 * Module.finrank K V + 2)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) : ∃ g : G, ρ g v = w := by
  letI : MulAction G V := MulAction.compHom V ρ
  letI : Fintype V := Fintype.ofFinite _
  have orbit_nonzero (a : V) (ha : a ≠ 0) : 0 ∉ MulAction.orbit G a := by
    rintro ⟨g, hg⟩
    apply ha
    exact (ρ g).injective (hg.trans (ρ g).map_zero.symm)
  have orbit_large (a : V) (ha : a ≠ 0) :
      Module.finrank K V < (MulAction.orbit G a).ncard := by
    let s := (MulAction.orbit G a).toFinset
    have hs : s.Nonempty := ⟨a, by
      simpa only [s, Set.mem_toFinset] using (MulAction.mem_orbit_self (M := G) a)⟩
    have hz : 0 ∉ s := by simpa only [s, Set.mem_toFinset] using orbit_nonzero a ha
    have hstable (g : G) (x : V) : ρ g x ∈ s ↔ x ∈ s := by
      change g • x ∈ (MulAction.orbit G a).toFinset ↔ x ∈ (MulAction.orbit G a).toFinset
      simp only [Set.mem_toFinset]
      constructor
      · intro hx
        simpa only [inv_smul_smul] using MulAction.mem_orbit_of_mem_orbit g⁻¹ hx
      · exact MulAction.mem_orbit_of_mem_orbit g
    have hb := IrreducibleLinearInvariantSmallSet.finrank_lt_card_of_invariant_nonzero_finset
      ρ hirr hdim s hs hz hstable
    simpa only [s, ← Set.ncard_eq_toFinset_card'] using hb
  by_contra hno
  have hwout : w ∉ MulAction.orbit G v := hno
  have hdis : Disjoint (MulAction.orbit G v) (MulAction.orbit G w) := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    apply hwout
    have he : MulAction.orbit G w = MulAction.orbit G v :=
      (MulAction.orbit_eq_iff.mpr hb).symm.trans (MulAction.orbit_eq_iff.mpr ha)
    rw [← he]
    exact MulAction.mem_orbit_self w
  have hsub : MulAction.orbit G v ∪ MulAction.orbit G w ⊆ ({0} : Set V)ᶜ := by
    intro a ha
    change a ∉ ({0} : Set V)
    intro haz
    have ha0 : a = 0 := Set.mem_singleton_iff.mp haz
    subst a
    exact ha.elim (orbit_nonzero v hv) (orbit_nonzero w hw)
  have hsum := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hdis] at hsum
  have htotal := Set.ncard_add_ncard_compl ({0} : Set V)
  rw [Set.ncard_singleton] at htotal
  have hvlarge := orbit_large v hv
  have hwlarge := orbit_large w hw
  omega

end SymmetricSubgroupAsymptotics.IrreducibleLinearSmallSpaceTransitivity
