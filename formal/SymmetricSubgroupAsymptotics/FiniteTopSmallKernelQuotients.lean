import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import Mathlib.GroupTheory.PGroup

/-! Original normal quotients of a finite extension with kernel order at
most four. Retained axes keep the SAME top. Axes meeting that top use the
actual residual quotient instead; no all-normal retention is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopSmallKernelQuotients
open OriginalKernelModuleChart
variable {G T : Type} [Group G] [Group T]
  (top : G →* T) (N : Subgroup G) [N.Normal]

def retainedTop (hN : N≤top.ker) : (G ⧸ N) →* T := QuotientGroup.lift N top hN

include top in
theorem retainedTop_surjective (htop : Function.Surjective top) (hN : N≤top.ker) :
    Function.Surjective (retainedTop top N hN) := by
  intro t
  obtain ⟨g,hg⟩ := htop t
  exact ⟨QuotientGroup.mk' N g,hg⟩

def retainedKernelMap (hN : N≤top.ker) : top.ker →* (retainedTop top N hN).ker where
  toFun k := ⟨QuotientGroup.mk' N k.val,by change top k.val=1; exact k.property⟩
  map_one' := Subtype.ext (QuotientGroup.mk' N).map_one
  map_mul' a b := Subtype.ext ((QuotientGroup.mk' N).map_mul a.val b.val)

theorem retainedKernelMap_surjective (hN : N≤top.ker) :
    Function.Surjective (retainedKernelMap top N hN) := by
  intro x
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective N x.val
  have hk : top g=1 := by
    have hx := x.property
    rw [←hg] at hx
    exact hx
  refine ⟨⟨g,hk⟩,?_⟩
  exact Subtype.ext hg

theorem retained_kernel_small [Finite G] (hN : N≤top.ker) (hK : IsPGroup 2 top.ker)
    (hcard : Nat.card top.ker≤4) :
    IsPGroup 2 (retainedTop top N hN).ker ∧ Nat.card (retainedTop top N hN).ker≤4 := by
  exact ⟨hK.of_surjective (retainedKernelMap top N hN) (retainedKernelMap_surjective top N hN),
    (Nat.card_le_card_of_surjective (retainedKernelMap top N hN)
      (retainedKernelMap_surjective top N hN)).trans hcard⟩

/-- When the actual residual top is at most two, the whole SAME original
quotient is binary and has order at most eight. -/
theorem residual_binary_small [Finite G] (hK : IsPGroup 2 top.ker) (hcard : Nat.card top.ker≤4)
    (hres : Nat.card (G ⧸ (top.ker ⊔ N))≤2) :
    IsPGroup 2 (G ⧸ N) ∧ Nat.card (G ⧸ N)≤8 := by
  let R := G ⧸ (top.ker ⊔ N)
  let f := base top N
  have hs := base_surjective top N
  have hk : IsPGroup 2 f.ker :=
    hK.of_surjective (quotientKernelMap top N) (quotientKernelMap_surjective top N)
  have hkc : Nat.card f.ker≤4 :=
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
  exact he.symm.le.trans ((Nat.mul_le_mul hkc hres).trans (by norm_num))

end SymmetricSubgroupAsymptotics.FiniteTopSmallKernelQuotients
