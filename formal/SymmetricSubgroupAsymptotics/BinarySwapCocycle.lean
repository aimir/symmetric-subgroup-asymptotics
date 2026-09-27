import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

/-! A cocycle on the actual two-block permutation module.

If the cocycle vanishes on the index-two block kernel, it is an actual
coboundary. No complement or splitting of the original group is used;
the chosen outside element may have order four or larger.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinarySwapCocycle

variable {G : Type} [Group G] (H : Subgroup G)
    (σ : Representation (ZMod 2) G (ZMod 2 × ZMod 2))

/-- The outside lift need not be an involution: its square lies in the
actual index-two kernel, where the original cocycle vanishes. -/
theorem exists_coboundary_of_zero_on_kernel
    (hindex : H.index=2)
    (hact : ∀ (g : G) (p : ZMod 2 × ZMod 2),
      σ g p=if g∈H then p else (p.2,p.1))
    (g₀ : G) (hg₀ : g₀∉H)
    (z : groupCohomology.cocycles₁ (Rep.of σ))
    (hz : ∀ g∈H,z g=0) :
    ∃ b : ZMod 2 × ZMod 2,∀ g : G,z g=σ g b-b := by
  classical
  have hmul (g h : G) : z (g*h)=σ g (z h)+z g :=
    (groupCohomology.mem_cocycles₁_iff _).mp z.property g h
  have hsquare := hmul g₀ g₀
  rw [hz _ (H.mul_self_mem_of_index_two hindex g₀),hact,if_neg hg₀] at hsquare
  have hsum : (z g₀).2+(z g₀).1=0 := congrArg Prod.fst hsquare.symm
  have hdiag : (z g₀).2=(z g₀).1 := by
    have he := eq_neg_of_add_eq_zero_left hsum
    simpa only [ZMod.neg_eq_self_mod_two] using he
  let b : ZMod 2 × ZMod 2 := (0,(z g₀).1)
  have hgvalue : z g₀=σ g₀ b-b := by
    rw [hact,if_neg hg₀]
    apply Prod.ext
    · simp [b]
    · simp [b,hdiag,ZMod.neg_eq_self_mod_two]
  refine ⟨b,?_⟩
  intro g
  by_cases hg : g∈H
  · rw [hz g hg,hact,if_pos hg,sub_self]
  · have hinv : g₀⁻¹∉H := by
      intro hm
      exact hg₀ (by simpa only [inv_inv] using H.inv_mem hm)
    have hh : g₀⁻¹*g∈H :=
      (H.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hinv hg)
    have he := hmul g₀ (g₀⁻¹*g)
    rw [mul_inv_cancel_left,hz _ hh,map_zero,zero_add] at he
    rw [he,hgvalue,hact,hact,if_neg hg₀,if_neg hg]

end SymmetricSubgroupAsymptotics.BinarySwapCocycle
