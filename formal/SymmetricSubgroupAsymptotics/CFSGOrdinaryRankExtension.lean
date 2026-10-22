import Mathlib.GroupTheory.Rank
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Ordinary group rank adds across a genuine surjective homomorphism.
The proof lifts actual generators of its target and retains actual kernel
generators. No normal-generator bound is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryRankExtension
variable {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]

theorem rank_le_kernel_add_target (f : G →* Q) (hf : Function.Surjective f) :
    Group.rank G ≤ Group.rank f.ker + Group.rank Q := by
  classical
  obtain ⟨A, hAc, hA⟩ := Group.rank_spec f.ker
  obtain ⟨B, hBc, hB⟩ := Group.rank_spec Q
  choose lift hlift using hf
  let t : Finset G := A.image f.ker.subtype ∪ B.image lift
  let H := Subgroup.closure (t : Set G)
  have hA_mem (a : f.ker) (ha : a ∈ A) : a.val ∈ H :=
    Subgroup.subset_closure (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
  have hB_mem (b : Q) (hb : b ∈ B) : lift b ∈ H :=
    Subgroup.subset_closure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  have hker : f.ker ≤ H := by
    have hle : Subgroup.closure (A : Set f.ker) ≤ H.comap f.ker.subtype := by
      apply (Subgroup.closure_le _).mpr
      exact hA_mem
    rw [hA] at hle
    intro a ha
    exact hle (show (⟨a, ha⟩ : f.ker) ∈ ⊤ from trivial)
  have himage : H.map f = ⊤ := by
    apply top_unique
    rw [← hB]
    apply (Subgroup.closure_le _).mpr
    intro b hb
    exact ⟨lift b, hB_mem b hb, hlift b⟩
  have hH : H = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, he⟩ := show f x ∈ H.map f by rw [himage]; trivial
    have hz : x * y⁻¹ ∈ f.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    simpa only [inv_mul_cancel_right] using H.mul_mem (hker hz) hy
  have ht : Subgroup.closure (t : Set G) = ⊤ := hH
  refine (Group.rank_le ht).trans ?_
  calc
    t.card ≤ (A.image f.ker.subtype).card + (B.image lift).card := Finset.card_union_le _ _
    _ ≤ A.card + B.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by rw [hAc, hBc]

theorem rank_le_kernel_add_range (f : G →* Q) :
    Group.rank G ≤ Group.rank f.ker + Group.rank f.range := by
  have h := rank_le_kernel_add_target f.rangeRestrict f.rangeRestrict_surjective
  rwa [Group.rank_congr (MulEquiv.subgroupCongr f.ker_rangeRestrict)] at h

end SymmetricSubgroupAsymptotics.CFSGOrdinaryRankExtension
