import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Preorder.Finite

/-! Every abelian quotient of a finite group is already the image of an
actual nilpotent subgroup. Minimality is among literal subgroups mapping
onto the same target; Frattini lifting forces every Sylow to be normal. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem exists_nilpotent_subgroup_surjective_abelian
    {G A : Type} [Group G] [Finite G] [CommGroup A]
    (f : G →* A) (hf : Function.Surjective f) :
    ∃ H : Subgroup G, Group.IsNilpotent H ∧
      Function.Surjective (f.comp H.subtype) := by
  let good : Subgroup G → Prop :=
    fun H => Function.Surjective (f.comp H.subtype)
  have htop : good ⊤ := by
    intro a
    obtain ⟨g, hg⟩ := hf a
    exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩
  obtain ⟨H, _, hmin⟩ := Finite.exists_le_minimal
    (p := good) (a := (⊤ : Subgroup G)) htop
  have hH : Function.Surjective (f.comp H.subtype) := hmin.1
  refine ⟨H, ?_, hH⟩
  apply ((Group.isNilpotent_of_finite_tfae (G := H)).out 0 3).mpr
  intro p hp P
  letI : Fact p.Prime := hp
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hNonto : Function.Surjective ((f.comp H.subtype).comp N.subtype) := by
    intro a
    have ha : a ∈ Subgroup.normalizer (((P : Subgroup H).map
        (f.comp H.subtype)) : Set A) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    obtain ⟨g, hgN, hga⟩ := SylowActualNormalizerLift.exists_lift
      (f.comp H.subtype) hH P a ha
    exact ⟨⟨g, hgN⟩, hga⟩
  have hgood : good (N.map H.subtype) := by
    intro a
    obtain ⟨n, hn⟩ := hNonto a
    exact ⟨⟨(n : H), ⟨n, n.property, rfl⟩⟩, hn⟩
  have hmap : N.map H.subtype = H :=
    hmin.eq_of_le hgood (Subgroup.map_subtype_le N)
  have hNtop : N = ⊤ := by
    apply top_unique
    intro h _
    have hh : (h : G) ∈ N.map H.subtype := by
      rw [hmap]
      exact h.property
    obtain ⟨n, hn, hnh⟩ := hh
    exact (Subtype.ext hnh : n = h) ▸ hn
  exact Subgroup.normalizer_eq_top_iff.mp hNtop

end SymmetricSubgroupAsymptotics
