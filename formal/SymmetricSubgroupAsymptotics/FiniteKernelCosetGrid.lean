import SymmetricSubgroupAsymptotics.FiniteGeneratedKernelTable

/-! A finite kernel table and quotient representatives cover the actual
preimage of a subgroup. No closure enumeration of the original group is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

 theorem exists_kernel_coset_grid
    {G H I J R : Type} [Group G] [Group H]
    {source : J → G} (T : FiniteGeneratedKernelTable (I := I) source)
    (f : G →* H) (hker : f.ker=T.subgroup)
    (B : Subgroup H) (lift : R → G)
    (hcover : ∀ h∈B, ∃ r, f (lift r)=h)
    (g : G) (hg : f g∈B) :
    ∃ r i, g=lift r*T.element i := by
  obtain ⟨r,hr⟩ := hcover (f g) hg
  have hk : (lift r)⁻¹*g∈T.subgroup := by
    rw [←hker]
    change f ((lift r)⁻¹*g)=1
    rw [map_mul,map_inv,hr,inv_mul_cancel]
  obtain ⟨i,hi⟩ := hk
  refine ⟨r,i,?_⟩
  rw [hi]
  simp only [mul_inv_cancel_left]

end SymmetricSubgroupAsymptotics
