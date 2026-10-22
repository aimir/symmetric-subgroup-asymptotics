import SymmetricSubgroupAsymptotics.CFSGNormalSubgroupSimpleProduct
import Mathlib.GroupTheory.Rank

/-! Actual ordinary generators of a finite product, with their coordinate
supports retained. This is ordinary group rank, not ambient normal rank. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteProductRank
variable {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Type*) [∀ i, Group (S i)]

 theorem closure_of_coordinate_family {J : I → Type*} (g : ∀ i, J i → S i)
    (hg : ∀ i, Subgroup.closure (Set.range (g i)) = ⊤) :
    Subgroup.closure (Set.range (fun p : Sigma J => Pi.mulSingle p.1 (g p.1 p.2))) = ⊤ := by
  classical
  let H := Subgroup.closure
    (Set.range (fun p : Sigma J => Pi.mulSingle p.1 (g p.1 p.2)))
  have hi (i : I) (a : S i) : Pi.mulSingle i a ∈ H := by
    let c : S i →* ∀ i, S i := MonoidHom.mulSingle S i
    have hle : Subgroup.closure (Set.range (g i)) ≤ H.comap c := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨⟨i, j⟩, rfl⟩
    rw [hg i] at hle
    exact hle (by trivial)
  apply top_unique
  intro x _
  rw [← Finset.noncommProd_mulSingle x]
  exact H.noncommProd_mem _ (fun i _ => hi i (x i))

 theorem rank_le_sum_rank [∀ i, Finite (S i)] :
    Group.rank (∀ i, S i) ≤ ∑ i, Group.rank (S i) := by
  classical
  choose t htcard ht using fun i => Group.rank_spec (S i)
  let J := fun i => {x : S i // x ∈ t i}
  let g : ∀ i, J i → S i := fun _ x => x.val
  have hg (i : I) : Subgroup.closure (Set.range (g i)) = ⊤ := by
    change Subgroup.closure (Set.range (Subtype.val : {x : S i // x ∈ t i} → S i)) = ⊤
    rw [Subtype.range_coe]
    exact ht i
  let a : Sigma J → ∀ i, S i := fun p => Pi.mulSingle p.1 (g p.1 p.2)
  have ha := closure_of_coordinate_family S g hg
  have hr := Subgroup.rank_closure_finite_le_nat_card (Set.range a)
  have he : Group.rank (Subgroup.closure (Set.range a)) = Group.rank (∀ i, S i) :=
    (Group.rank_congr (MulEquiv.subgroupCongr ha)).trans
      (Group.rank_congr Subgroup.topEquiv)
  rw [he] at hr
  have hcard : Nat.card (Set.range a) ≤ Nat.card (Sigma J) :=
    Nat.card_le_card_of_surjective (Set.rangeFactorization a) (Set.rangeFactorization_surjective (f := a))
  refine hr.trans (hcard.trans ?_)
  rw [Nat.card_sigma]
  exact Finset.sum_le_sum fun i _ => by simpa only [J, Nat.card_eq_fintype_card,
    Fintype.card_coe] using (le_of_eq (htcard i))

end SymmetricSubgroupAsymptotics.CFSGFiniteProductRank
