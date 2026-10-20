import SymmetricSubgroupAsymptotics.SchreierKernelSubtypeGenerators
import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! A selected finite quotient section controls the SAME original kernel
coordinates through its Schreier words. No original group closure/table
or normal census is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G Q V ι : Type} [Group G] [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {chi : G →* Q} {A : Rep.{0} (ZMod 2) Q} (E : OriginalKernelModuleChart chi A)
    (j : A →ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V)
    (g : ι → G) (hg : Subgroup.closure (Set.range g)=⊤)
    (r : Q → G) (hr : ∀ q,chi (r q)=q) (hr1 : r 1=1)

include hg hr1 in
theorem coordinates_mem_of_schreier
    (hwords : ∀ t : Q × ι,
      j (E.equiv.symm (schreierKernelGenerators g chi r hr t)).toAdd∈W) :
    ∀ x : chi.ker,j (E.equiv.symm x).toAdd∈W := by
  let L : Subgroup chi.ker :=
    { carrier := {x | j (E.equiv.symm x).toAdd∈W}
      one_mem' := by
        change j (E.equiv.symm 1).toAdd∈W
        rw [map_one]
        change j 0∈W
        rw [map_zero]
        exact W.zero_mem
      mul_mem' := by
        intro x y hx hy
        change j (E.equiv.symm (x*y)).toAdd∈W
        rw [map_mul]
        change j ((E.equiv.symm x).toAdd+(E.equiv.symm y).toAdd)∈W
        rw [map_add]
        exact W.add_mem hx hy
      inv_mem' := by
        intro x hx
        change j (E.equiv.symm x⁻¹).toAdd∈W
        rw [map_inv]
        change j (-(E.equiv.symm x).toAdd)∈W
        rw [map_neg]
        exact W.neg_mem hx }
  have hle : Subgroup.closure (Set.range (schreierKernelGenerators g chi r hr))≤L := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact hwords t
  rw [schreierKernelGenerators_generate g hg chi r hr hr1] at hle
  intro x
  exact hle (Subgroup.mem_top x)
end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
