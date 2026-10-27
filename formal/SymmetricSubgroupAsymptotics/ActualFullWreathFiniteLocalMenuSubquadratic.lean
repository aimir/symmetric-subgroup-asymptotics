import SymmetricSubgroupAsymptotics.ActualFullWreathFixedLocalSubquadratic

/-! A finite labelled menu of genuine fixed local groups inherits ONE
threshold. In particular all literal local permutation subgroups up to a
fixed degree are covered. This is finite bookkeeping, not an extra
bounded-local counting hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualFullWreathFiniteLocalMenuSubquadratic
open ActualFullWreathFamily ActualFullWreathFixedLocalSubquadratic

theorem finite_menu (hCFSG : CFSG.CFSGClassification)
    {J : Type} [Fintype J] (R : J → Type) [∀j,Group (R j)] [∀j,Finite (R j)]
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ j : J,∀ (Q I : Type) [Group Q] [Fintype I]
      [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I],
      N≤Nat.card I →
      (Nat.card (Family (R j) Q I) : ℝ)≤(2 : ℝ)^(ε*(Nat.card I : ℝ)^2) := by
  choose n hn using (fun j : J => fixed_local_group_subquadratic hCFSG (R j) ε hε)
  refine ⟨Finset.univ.sup n,?_⟩
  intro j Q I _ _ _ _ _ hI
  exact hn j Q I ((Finset.le_sup (f := n) (Finset.mem_univ j)).trans hI)

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

abbrev BoundedLocalIndex (k : ℕ) := Σ r : Fin (k+1),Subgroup (Equiv.Perm (Fin r.val))

theorem bounded_permutation_locals (hCFSG : CFSG.CFSGClassification) (k : ℕ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ r : ℕ,r≤k → ∀ D : Subgroup (Equiv.Perm (Fin r)),
      ∀ (Q I : Type) [Group Q] [Fintype I]
        [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I],
        N≤Nat.card I →
        (Nat.card (Family D Q I) : ℝ)≤(2 : ℝ)^(ε*(Nat.card I : ℝ)^2) := by
  letI : Fintype (BoundedLocalIndex k) := Fintype.ofFinite _
  obtain ⟨N,hN⟩ := finite_menu hCFSG (fun j : BoundedLocalIndex k => j.2) ε hε
  refine ⟨N,?_⟩
  intro r hr D Q I _ _ _ _ _ hI
  let j : BoundedLocalIndex k := ⟨⟨r,Nat.lt_succ_of_le hr⟩,D⟩
  exact hN j Q I hI

end SymmetricSubgroupAsymptotics.ActualFullWreathFiniteLocalMenuSubquadratic
