import SymmetricSubgroupAsymptotics.FiniteTopSmallKernelQuotients

/-! Arbitrary finite bounds on the SAME original binary kernel descend
through every original normal axis. Only the actual residual top is used
when the denominator meets the top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopBoundedBinaryKernelQuotients
open OriginalKernelModuleChart FiniteTopSmallKernelQuotients
variable {G T : Type} [Group G] [Group T]
  (top : G →* T) (N : Subgroup G) [N.Normal]

theorem retained_kernel_bounded [Finite G] (M : ℕ) (hN : N≤top.ker) (hK : IsPGroup 2 top.ker)
    (hcard : Nat.card top.ker≤M) :
    IsPGroup 2 (retainedTop top N hN).ker ∧ Nat.card (retainedTop top N hN).ker≤M := by
  exact ⟨hK.of_surjective (retainedKernelMap top N hN) (retainedKernelMap_surjective top N hN),
    (Nat.card_le_card_of_surjective (retainedKernelMap top N hN)
      (retainedKernelMap_surjective top N hN)).trans hcard⟩

/-- The actual residual top of order at most two costs a factor at most two. -/
theorem residual_binary_bounded [Finite G] (M : ℕ) (hK : IsPGroup 2 top.ker) (hcard : Nat.card top.ker≤M)
    (hres : Nat.card (G ⧸ (top.ker ⊔ N))≤2) :
    IsPGroup 2 (G ⧸ N) ∧ Nat.card (G ⧸ N)≤M*2 := by
  let R := G ⧸ (top.ker ⊔ N)
  let f := base top N
  have hs := base_surjective top N
  have hk : IsPGroup 2 f.ker :=
    hK.of_surjective (quotientKernelMap top N) (quotientKernelMap_surjective top N)
  have hkc : Nat.card f.ker≤M :=
    (Nat.card_le_card_of_surjective (quotientKernelMap top N)
      (quotientKernelMap_surjective top N)).trans hcard
  have hcR : Nat.card R≤2 := hres
  have hR : IsPGroup 2 R := by
    have hp : 0<Nat.card R := Nat.card_pos
    by_cases h1 : Nat.card R=1
    · exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · have h2 : Nat.card R=2 := by omega
      exact IsPGroup.of_card (n := 1) (by simpa using h2)
  have hQ := (hR.to_subgroup (⊤ : Subgroup R)).comap_of_ker_isPGroup f hk
  have hQt : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := by
    simpa only [Subgroup.comap_top] using hQ
  refine ⟨hQt.of_equiv Subgroup.topEquiv,?_⟩
  have he := f.ker.card_mul_index
  rw [Subgroup.index_ker,f.range_eq_top_of_surjective hs,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at he
  exact he.symm.le.trans (Nat.mul_le_mul hkc hres)

end SymmetricSubgroupAsymptotics.FiniteTopBoundedBinaryKernelQuotients
