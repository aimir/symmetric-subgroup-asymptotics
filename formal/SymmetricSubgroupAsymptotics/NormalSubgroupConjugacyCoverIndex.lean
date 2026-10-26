import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.Group

/-! An ambient conjugacy cover of a normal subgroup loses at most its
actual index when counted as conjugacy classes INSIDE that subgroup.
Fixed quotient representatives supply the missing conjugator coset.
No ambient class-count bound or class monotonicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyCoverIndex

variable {G : Type*} [Group G] [Finite G] (H : Subgroup G) [H.Normal]

theorem class_card_le_index_mul_family {C : Type*} [Finite C]
    (rep : C → H)
    (hcover : ∀ h : H,∃ c : C,IsConj (rep c : G) (h : G)) :
    Nat.card (ConjClasses H) ≤ H.index * Nat.card C := by
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  let r : G ⧸ H → G := fun z => Classical.choose (QuotientGroup.mk'_surjective H z)
  have hr (z : G ⧸ H) : q (r z)=z :=
    Classical.choose_spec (QuotientGroup.mk'_surjective H z)
  let carrier : (G ⧸ H) × C → H := fun z =>
    ⟨r z.1*(rep z.2 : G)*(r z.1)⁻¹,
      (inferInstance : H.Normal).conj_mem (rep z.2 : G) (rep z.2).property (r z.1)⟩
  let f : (G ⧸ H) × C → ConjClasses H := fun z => ConjClasses.mk (carrier z)
  have hf : Function.Surjective f := by
    intro k
    obtain ⟨h,rfl⟩ := ConjClasses.mk_surjective k
    obtain ⟨c,hc⟩ := hcover h
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    let z : G ⧸ H := q g
    let a : G := g*(r z)⁻¹
    have ha : a∈H := by
      apply (QuotientGroup.eq_one_iff a).mp
      change q a=1
      dsimp only [a]
      rw [map_mul,map_inv,hr]
      exact mul_inv_cancel (q g)
    let ah : H := ⟨a,ha⟩
    have he : ah*carrier (z,c)*ah⁻¹=h := by
      apply Subtype.ext
      change a*(r z*(rep c : G)*(r z)⁻¹)*a⁻¹=(h : G)
      calc
        _=g*(rep c : G)*g⁻¹ := by dsimp only [a]; group
        _=(h : G) := hg
    refine ⟨(z,c),?_⟩
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨ah,he⟩)
  calc
    _≤Nat.card ((G ⧸ H) × C) := Nat.card_le_card_of_surjective f hf
    _=H.index * Nat.card C := by rw [Nat.card_prod,←H.index_eq_card]

theorem class_card_le_index_mul_card (C : Finset H)
    (hcover : ∀ h : H,∃ c∈C,IsConj (c : G) (h : G)) :
    Nat.card (ConjClasses H) ≤ H.index * C.card := by
  have hh := class_card_le_index_mul_family H
    (fun c : {c : H // c∈C} => c.val) (by
      intro h
      obtain ⟨c,hc,he⟩ := hcover h
      exact ⟨⟨c,hc⟩,he⟩)
  have hc : Nat.card {c : H // c∈C}=C.card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  simpa only [hc] using hh

end SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyCoverIndex
