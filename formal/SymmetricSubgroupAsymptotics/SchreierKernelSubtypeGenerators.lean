import SymmetricSubgroupAsymptotics.SchreierKernelGenerators

/-! Schreier words as elements of the exact original homomorphism kernel.
The closure theorem is internal to that kernel and can feed a selected
finite quotient-word graph without replacing the original group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G Q ι : Type*} [Group G] [Group Q]

def schreierKernelGenerators (g : ι → G) (χ : G →* Q)
    (r : Q → G) (hr : ∀ q, χ (r q) = q) : Q × ι → χ.ker :=
  fun x => ⟨schreierWords g χ r x, by
    apply MonoidHom.mem_ker.mpr
    simp only [schreierWords, map_mul, map_inv, hr, mul_inv_cancel]⟩

theorem schreierKernelGenerators_generate (g : ι → G)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (χ : G →* Q) (r : Q → G) (hr : ∀ q, χ (r q) = q)
    (hr1 : r 1 = 1) :
    Subgroup.closure (Set.range (schreierKernelGenerators g χ r hr)) = ⊤ := by
  apply Subgroup.map_injective χ.ker.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  have he : χ.ker.subtype ∘ schreierKernelGenerators g χ r hr =
      schreierWords g χ r := rfl
  rw [he, ← schreier_kernel_generated g hg χ r hr hr1]
  simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics
