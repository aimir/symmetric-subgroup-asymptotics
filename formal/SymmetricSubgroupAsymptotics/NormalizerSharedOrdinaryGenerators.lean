import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! If a normal subgroup `E` normalizes `A` and is the normal closure of
`A`, ordinary generators of `A` together with lifts of generators of `G/E`
generate `G`. This uses the normalizer hypothesis explicitly; it does not
replace ordinary generation of a general normal kernel by normal generation.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NormalizerSharedOrdinaryGenerators

variable {G : Type} [Group G]

theorem eq_top_of_map_eq_top (E A H : Subgroup G) [E.Normal]
    (hnorm : E ≤ Subgroup.normalizer A)
    (hclosure : Subgroup.normalClosure (A : Set G) = E)
    (hA : A ≤ H) (hmap : H.map (QuotientGroup.mk' E) = ⊤) : H = ⊤ := by
  have hconj : ∀ g a : G, a ∈ A → g*a*g⁻¹ ∈ H := by
    intro g a ha
    obtain ⟨h,hh,hhg⟩ : (g : G⧸E) ∈ H.map (QuotientGroup.mk' E) := by
      rw [hmap]
      trivial
    have he : h⁻¹*g ∈ E := by
      rw [← QuotientGroup.eq]
      exact hhg
    have hmem : (h⁻¹*g)*a*(h⁻¹*g)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hnorm he) a).mp ha
    have heq : g*a*g⁻¹ = h*((h⁻¹*g)*a*(h⁻¹*g)⁻¹)*h⁻¹ := by group
    rw [heq]
    exact H.mul_mem (H.mul_mem hh (hA hmem)) (H.inv_mem hh)
  have hE : E ≤ H := by
    rw [← hclosure, Subgroup.normalClosure]
    apply (Subgroup.closure_le H).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    exact hconj g a ha
  apply top_unique
  intro x _
  obtain ⟨h,hh,hhx⟩ : (x : G⧸E) ∈ H.map (QuotientGroup.mk' E) := by
    rw [hmap]
    trivial
  have he : h⁻¹*x ∈ E := by
    rw [← QuotientGroup.eq]
    exact hhx
  have hx : x=h*(h⁻¹*x) := by group
  rw [hx]
  exact H.mul_mem hh (hE he)

theorem exists_generating_finset [Finite G] (E A : Subgroup G) [E.Normal]
    (hnorm : E ≤ Subgroup.normalizer A)
    (hclosure : Subgroup.normalClosure (A : Set G) = E) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ MarkedC4.genRank A + MarkedC4.genRank (G⧸E) := by
  obtain ⟨s,hs,hscl⟩ := MarkedC4.genRank_spec (G:=A)
  obtain ⟨t,ht,htcl⟩ := MarkedC4.genRank_spec (G:=G⧸E)
  let lift : G⧸E → G := Quotient.out
  let S : Finset G := s.image A.subtype ∪ t.image lift
  let H : Subgroup G := Subgroup.closure (S : Set G)
  have hA : A ≤ H := by
    intro a ha
    have hm : (⟨a,ha⟩ : A) ∈ Subgroup.closure (s : Set A) := by
      rw [hscl]
      trivial
    have hi := Subgroup.mem_map_of_mem A.subtype hm
    rw [MonoidHom.map_closure] at hi
    refine (Subgroup.closure_mono ?_) hi
    intro y hy
    simp only [S, Finset.coe_union, Finset.coe_image]
    exact Or.inl hy
  have hmap : H.map (QuotientGroup.mk' E) = ⊤ := by
    rw [eq_top_iff, ← htcl, Subgroup.closure_le]
    intro q hq
    refine ⟨lift q,Subgroup.subset_closure ?_,QuotientGroup.out_eq' q⟩
    simp only [S, Finset.coe_union, Finset.coe_image]
    exact Or.inr ⟨q,hq,rfl⟩
  refine ⟨S,eq_top_of_map_eq_top E A H hnorm hclosure hA hmap,?_⟩
  calc
    S.card ≤ (s.image A.subtype).card+(t.image lift).card := Finset.card_union_le _ _
    _ ≤ s.card+t.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = MarkedC4.genRank A+MarkedC4.genRank (G⧸E) := by rw [hs,ht]

theorem genRank_le [Finite G] (E A : Subgroup G) [E.Normal]
    (hnorm : E ≤ Subgroup.normalizer A)
    (hclosure : Subgroup.normalClosure (A : Set G) = E) :
    MarkedC4.genRank G ≤ MarkedC4.genRank A + MarkedC4.genRank (G⧸E) := by
  obtain ⟨S,hgen,hcard⟩ := exists_generating_finset E A hnorm hclosure
  exact (MarkedC4.genRank_le hgen).trans hcard

end SymmetricSubgroupAsymptotics.NormalizerSharedOrdinaryGenerators
