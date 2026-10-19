import SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature

/-! Reindex an actual finite kernel signature by a supplied exact chart.
This permits small computable receipts without evaluating a noncomputable
Fintype instance on a subgroup of the original permutation group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature
variable {R G I : Type} [Group R] [Group G] [Fintype R] [Fintype I]
  (kappa : R →* G) (code : G → ℕ) (enumerate : I → R)
  (henumerate : Function.Surjective enumerate)

include henumerate

theorem codes_eq_indexed (g : G) : codes kappa code g=
    Finset.univ.image (fun i : I => code (g*kappa (enumerate i))) := by
  ext n
  constructor
  · intro hn
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hn
    obtain ⟨i,rfl⟩ := henumerate r
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hr⟩
  · intro hn
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨enumerate i,Finset.mem_univ _,hi⟩

end SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature
