import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

/-! Schreier generation on the original group. Exact section values and
original generator images suffice to generate the full literal kernel.
For index two, the certificate has only two words per source generator;
no group order or complete element table is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G Q ι : Type*} [Group G] [Group Q]

def schreierWords (g : ι → G) (χ : G →* Q) (r : Q → G) : Q × ι → G :=
  fun x => r x.1 * g x.2 * (r (x.1 * χ (g x.2)))⁻¹

theorem schreier_kernel_generated (g : ι → G)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (χ : G →* Q) (r : Q → G) (hr : ∀ q, χ (r q) = q) (hr1 : r 1 = 1) :
    χ.ker = Subgroup.closure (Set.range (schreierWords g χ r)) := by
  let H := Subgroup.closure (Set.range (schreierWords g χ r))
  let S : Subgroup G :=
    { carrier := {a | ∀ q, r q*a*(r (q*χ a))⁻¹∈H}
      one_mem' := by intro q; simpa using H.one_mem
      mul_mem' := by
        intro a b ha hb q
        have ht := H.mul_mem (ha q) (hb (q*χ a))
        simpa only [map_mul,mul_assoc,inv_mul_cancel_left] using ht
      inv_mem' := by
        intro a ha q
        have ht := H.inv_mem (ha (q*(χ a)⁻¹))
        simpa only [map_inv,mul_assoc,inv_mul_cancel,mul_one,
          mul_inv_rev,inv_inv] using ht }
  have hS : Subgroup.closure (Set.range g) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩ q
    exact Subgroup.subset_closure ⟨(q,i),rfl⟩
  apply le_antisymm
  · intro a ha
    have ht := hS (hg ▸ (show a∈(⊤:Subgroup G) from trivial)) 1
    simpa only [hr1,one_mul,show χ a=1 from ha,inv_one,mul_one] using ht
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨q,i⟩,rfl⟩
    apply MonoidHom.mem_ker.mpr
    simp only [schreierWords,map_mul,map_inv,hr,mul_inv_cancel]

end SymmetricSubgroupAsymptotics
