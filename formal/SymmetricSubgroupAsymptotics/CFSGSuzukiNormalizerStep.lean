import SymmetricSubgroupAsymptotics.CFSGSuzukiAutomorphismTransport
import SymmetricSubgroupAsymptotics.CFSGSolubleGenerationLifting

/-! Suzuki's literal normalizer step. The intersection with the original
characteristic semisimple subgroup recovers the original chosen subgroup,
which proves both properness and self-normalization without replacing the
ambient source or adding a maximality assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem two_conjugates_generate_subtype {G : Type*} [Group G]
    (E : Subgroup G) (H : Subgroup E) (x : E)
    (hgen : Subgroup.closure ((H : Set E) ∪ H.map (MulAut.conj x).toMonoidHom) = ⊤) :
    Subgroup.closure (((H.map E.subtype) : Set G) ∪
      (H.map E.subtype).map (MulAut.conj (x : G)).toMonoidHom) = E := by
  let K := Subgroup.closure (((H.map E.subtype) : Set G) ∪
    (H.map E.subtype).map (MulAut.conj (x : G)).toMonoidHom)
  have hHE : H.map E.subtype ≤ E := by rintro _ ⟨h, _, rfl⟩; exact h.property
  apply le_antisymm
  · exact (Subgroup.closure_le E).mpr
      (Set.union_subset hHE (conjugate_le_of_mem x.property hHE))
  · have hle : Subgroup.closure ((H : Set E) ∪
        H.map (MulAut.conj x).toMonoidHom) ≤ K.comap E.subtype := by
      apply (Subgroup.closure_le _).mpr
      apply Set.union_subset
      · intro h hh
        exact Subgroup.subset_closure (Or.inl ⟨h, hh, rfl⟩)
      · rintro _ ⟨h, hh, rfl⟩
        exact Subgroup.subset_closure (Or.inr ⟨(h : G), ⟨h, hh, rfl⟩, rfl⟩)
    rw [hgen] at hle
    intro g hg
    exact hle (Subgroup.mem_top (⟨g, hg⟩ : E))

theorem normalizer_subtype_intersection {G : Type*} [Group G]
    (E : Subgroup G) (H : Subgroup E)
    (hself : Subgroup.normalizer (H : Set E) = H) :
    Subgroup.normalizer (H.map E.subtype : Set G) ⊓ E = H.map E.subtype := by
  let P := H.map E.subtype
  have hrange : P ≤ E.subtype.range := by
    rintro _ ⟨h, _, rfl⟩
    exact ⟨h, rfl⟩
  have hc : (Subgroup.normalizer (P : Set G)).comap E.subtype =
      Subgroup.normalizer (H : Set E) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (f := E.subtype) hrange]
    change Subgroup.normalizer (((H.map E.subtype).comap E.subtype) : Set E) = _
    rw [Subgroup.comap_map_eq_self_of_injective (f := E.subtype) Subtype.val_injective]
  have he := Subgroup.subgroupOf_map_subtype (Subgroup.normalizer (P : Set G)) E
  change ((Subgroup.normalizer (P : Set G)).comap E.subtype).map E.subtype =
    Subgroup.normalizer (P : Set G) ⊓ E at he
  rw [hc, hself] at he
  exact he.symm

theorem chosen_normalizer_proper_of_radical_free {G : Type*} [Group G] [Finite G]
    (hR : solubleRadical G = ⊥) (E : Subgroup G) (hE : E ≠ ⊥)
    (H : Subgroup E) (hsol : IsSolvable H)
    (hself : Subgroup.normalizer (H : Set E) = H) :
    Subgroup.normalizer (H.map E.subtype : Set G) ≠ ⊤ := by
  let P := H.map E.subtype
  intro ht
  letI suzukiProper_solubleH : IsSolvable H := hsol
  letI suzukiProper_solubleP : IsSolvable P := soluble_subgroup_map E.subtype H
  letI suzukiProper_normalP : P.Normal := Subgroup.normalizer_eq_top_iff.mp ht
  have hP : P = ⊥ := by
    apply le_bot_iff.mp
    rw [← hR]
    exact le_solubleRadical P
  have hi := normalizer_subtype_intersection E H hself
  change Subgroup.normalizer (P : Set G) ⊓ E = P at hi
  rw [ht, top_inf_eq, hP] at hi
  exact hE hi

theorem radical_normalizer_contains_original {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (H : Subgroup E) (hsol : IsSolvable H)
    (S : Subgroup (Subgroup.normalizer (H.map E.subtype : Set G)))
    (hRad : solubleRadical (Subgroup.normalizer (H.map E.subtype : Set G)) ≤ S) :
    H.map E.subtype ≤ S.map (Subgroup.normalizer (H.map E.subtype : Set G)).subtype := by
  let P := H.map E.subtype
  let N := Subgroup.normalizer (P : Set G)
  letI suzukiContain_solubleH : IsSolvable H := hsol
  letI suzukiContain_solubleP : IsSolvable P := soluble_subgroup_map E.subtype H
  let e := Subgroup.subgroupOfEquivOfLe (show P ≤ N from Subgroup.le_normalizer)
  letI suzukiContain_solubleInN : IsSolvable (P.subgroupOf N) :=
    solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have hle : P.subgroupOf N ≤ S := (le_solubleRadical (P.subgroupOf N)).trans hRad
  intro p hp
  exact ⟨⟨p, Subgroup.le_normalizer hp⟩, hle hp, rfl⟩

theorem self_normalizing_normalizer_step {G : Type*} [Group G]
    (E : Subgroup G) [E.Normal] (H : Subgroup E)
    (hHself : Subgroup.normalizer (H : Set E) = H)
    (S₀ : Subgroup (Subgroup.normalizer (H.map E.subtype : Set G)))
    (hPS : H.map E.subtype ≤ S₀.map (Subgroup.normalizer (H.map E.subtype : Set G)).subtype)
    (hSself : Subgroup.normalizer (S₀ : Set (Subgroup.normalizer (H.map E.subtype : Set G))) = S₀) :
    Subgroup.normalizer
      (S₀.map (Subgroup.normalizer (H.map E.subtype : Set G)).subtype : Set G) =
        S₀.map (Subgroup.normalizer (H.map E.subtype : Set G)).subtype := by
  let P := H.map E.subtype
  let N := Subgroup.normalizer (P : Set G)
  let S := S₀.map N.subtype
  have hSN : S ≤ N := by rintro _ ⟨s, _, rfl⟩; exact s.property
  have hPE : P ≤ E := by rintro _ ⟨h, _, rfl⟩; exact h.property
  have hNE : N ⊓ E = P := normalizer_subtype_intersection E H hHself
  have hSE : S ⊓ E = P :=
    le_antisymm ((inf_le_inf hSN le_rfl).trans_eq hNE) (le_inf hPS hPE)
  have hnorm : Subgroup.normalizer (S : Set G) ≤ N := by
    intro g hg
    have hE : g ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.normalizer_eq_top E]
      exact Subgroup.mem_top _
    have h := (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := E)) ⟨hg, hE⟩
    rw [hSE] at h
    exact h
  have hsub : S.subgroupOf N = S₀ := by
    change (S₀.map N.subtype).comap N.subtype = S₀
    exact Subgroup.comap_map_eq_self_of_injective (f := N.subtype) Subtype.val_injective S₀
  apply le_antisymm
  · intro g hg
    let v : N := ⟨g, hnorm hg⟩
    have hv : v ∈ (Subgroup.normalizer (S : Set G)).subgroupOf N := hg
    rw [Subgroup.subgroupOf_normalizer_eq hSN, hsub, hSself] at hv
    exact ⟨v, hv, rfl⟩
  · exact Subgroup.le_normalizer

theorem suzuki_normalizer_step {G : Type*} [Group G] [Finite G]
    (hR : solubleRadical G = ⊥) (E : Subgroup G) [E.Characteristic]
    (H : Subgroup E) (x : E) (hHsol : IsSolvable H) (hHinv : Intravariant H)
    (hHself : Subgroup.normalizer (H : Set E) = H)
    (hEgen : Subgroup.closure ((H : Set E) ∪ H.map (MulAut.conj x).toMonoidHom) = ⊤)
    (S : Subgroup (Subgroup.normalizer (H.map E.subtype : Set G)))
    (y : Subgroup.normalizer (H.map E.subtype : Set G))
    (hSsol : IsSolvable S) (hSinv : Intravariant S)
    (hSself : Subgroup.normalizer (S : Set (Subgroup.normalizer (H.map E.subtype : Set G))) = S)
    (hSrad : solubleRadical (Subgroup.normalizer (H.map E.subtype : Set G)) ≤ S)
    (hNgen : Subgroup.closure ((S : Set (Subgroup.normalizer (H.map E.subtype : Set G))) ∪
      S.map (MulAut.conj y).toMonoidHom) = ⊤) :
    ∃ (S' : Subgroup G) (g : G), IsSolvable S' ∧ Intravariant S' ∧
      Subgroup.normalizer (S' : Set G) = S' ∧ solubleRadical G ≤ S' ∧
        Subgroup.closure ((S' : Set G) ∪ S'.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let N := Subgroup.normalizer (H.map E.subtype : Set G)
  have hPS := radical_normalizer_contains_original E H hHsol S hSrad
  letI suzukiNormalizer_solubleS : IsSolvable S := hSsol
  refine ⟨S.map N.subtype, (x : G) * y, soluble_subgroup_map N.subtype S,
    intravariant_normalizer_step E H hHinv S hSinv,
    self_normalizing_normalizer_step E H hHself S hPS hSself, ?_, ?_⟩
  · rw [hR]
    exact bot_le
  · exact two_conjugates_generate_of_normal_intravariant E H (S.map N.subtype) x y
      hHinv hPS y.property (two_conjugates_generate_subtype E H x hEgen)
      (two_conjugates_generate_subtype N S y hNgen)

end SymmetricSubgroupAsymptotics.CFSGReduction
