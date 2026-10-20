import SymmetricSubgroupAsymptotics.SchreierKernelSubtypeGenerators
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem schreier_kernel_image_mem {G Q H ι : Type} [Group G] [Group Q] [Group H]
    (g : ι → G) (hg : Subgroup.closure (Set.range g)=⊤)
    (chi : G →* Q) (r : Q → G) (hr : ∀ q,chi (r q)=q) (hr1 : r 1=1)
    (f : G →* H) (W : Subgroup H)
    (hwords : ∀ t : Q × ι,f (schreierWords g chi r t)∈W) :
    ∀ k : chi.ker,f k.val∈W := by
  let s := schreierKernelGenerators g chi r hr
  have hle : Subgroup.closure (Set.range s)≤W.comap (f.comp chi.ker.subtype) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    change f (schreierWords g chi r t) ∈ W
    exact hwords t
  have hs : Subgroup.closure (Set.range s)=⊤ :=
    schreierKernelGenerators_generate g hg chi r hr hr1
  rw [hs] at hle
  exact fun k => hle (Subgroup.mem_top k)
end SymmetricSubgroupAsymptotics
