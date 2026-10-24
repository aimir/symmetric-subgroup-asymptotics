import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Ordinary generators from a finite family of ACTUAL parameter
homomorphisms whose ranges generate the original group. This is an
ordinary union of finite generating sets; no normal-generation number,
independence of ranges, or direct-product assertion is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteHomFamilyOrdinaryGenerators

variable {I : Type*} [Fintype I] (A : I → Type*)
    [∀ i, Group (A i)] [∀ i, Finite (A i)]
    {G : Type*} [Group G] [Finite G] (f : ∀ i, A i →* G)
    (hgen : (⨆ i, (f i).range) = ⊤)

include f hgen

theorem exists_generating_finset :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ ∑ i, MarkedC4.genRank (A i) := by
  choose s hsCard hsGen using (fun i => MarkedC4.genRank_spec (G := A i))
  let S : Finset G := Finset.univ.biUnion (fun i => (s i).image (f i))
  have hS : Subgroup.closure (S : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply iSup_le
    intro i y hy
    obtain ⟨x,rfl⟩ := hy
    have hsi : (s i : Set (A i)) ⊆
        (Subgroup.closure (S : Set G)).comap (f i) := by
      intro a ha
      apply Subgroup.subset_closure
      change f i a ∈ Finset.univ.biUnion (fun j => (s j).image (f j))
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
        Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
    have hle := (Subgroup.closure_le _).mpr hsi
    rw [hsGen i] at hle
    exact hle (Subgroup.mem_top x)
  have hcard : S.card ≤ ∑ i, MarkedC4.genRank (A i) := by
    calc
      S.card ≤ ∑ i, ((s i).image (f i)).card := Finset.card_biUnion_le
      _ ≤ ∑ i, (s i).card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)
      _ = ∑ i, MarkedC4.genRank (A i) := Finset.sum_congr rfl (fun i _ => hsCard i)
  exact ⟨S,hS,hcard⟩

theorem genRank_le_sum :
    MarkedC4.genRank G ≤ ∑ i, MarkedC4.genRank (A i) := by
  obtain ⟨S,hS,hcard⟩ := exists_generating_finset A f hgen
  exact (MarkedC4.genRank_le hS).trans hcard

end SymmetricSubgroupAsymptotics.FiniteHomFamilyOrdinaryGenerators
