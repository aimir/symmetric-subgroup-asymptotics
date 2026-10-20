import SymmetricSubgroupAsymptotics.FiniteGeneratorGraphStateContainment
import SymmetricSubgroupAsymptotics.SchreierKernelSubtypeGenerators
import SymmetricSubgroupAsymptotics.IndexTwoSchreier
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Exact original twelve-point row181 block kernel. The two components
are related by the checked word graph, not ordinary point conjugacy.
This file does not supply a socle bound or alter an original denominator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

abbrev Original := Row181Top
abbrev generators := row181Generators

def pointFrame : Fin 2 × Fin 6 ≃ Fin 12 :=
  (Equiv.prodComm (Fin 2) (Fin 6)).trans finProdFinEquiv

def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def tops : Fin 3 → Equiv.Perm (Fin 2) := ![1, 1, swap]

private theorem frame_checked : ∀ (j : Fin 3) (p : Fin 2 × Fin 6),
    (pointFrame.symm (generators j (pointFrame p))).1 = tops j p.1 := by
  decide +kernel

def blockFrame : ProductBlockFrame Original (Fin 2) (Fin 6) :=
  ProductBlockFrame.ofGenerators pointFrame generators tops frame_checked

def originalGenerator : Fin 3 → Original := originalGeneratedGenerators generators

private theorem top_generator (j : Fin 3) :
    blockFrame.top (originalGenerator j) = tops j :=
  ProductBlockFrame.ofGenerators_top_generator pointFrame generators tops frame_checked j

def rawKernelGenerators : Fin 9 → Original :=
  ![originalGenerator 0, originalGenerator 1,
    originalGenerator 2 * originalGenerator 2,
    (originalGenerator 0)⁻¹, (originalGenerator 1)⁻¹,
    originalGenerator 2 * originalGenerator 0 * (originalGenerator 2)⁻¹,
    originalGenerator 2 * originalGenerator 1 * (originalGenerator 2)⁻¹,
    originalGenerator 2 * (originalGenerator 0)⁻¹ * (originalGenerator 2)⁻¹,
    originalGenerator 2 * (originalGenerator 1)⁻¹ * (originalGenerator 2)⁻¹]

private theorem top_raw : ∀ j, blockFrame.top (rawKernelGenerators j) = 1 := by
  intro j
  have hs : swap * swap = 1 := by decide +kernel
  fin_cases j <;> simp [rawKernelGenerators, map_mul, map_inv, top_generator, tops, hs]

def kernelGenerators (j : Fin 9) : blockFrame.top.ker :=
  ⟨rawKernelGenerators j, top_raw j⟩

private theorem swap_ne_one : swap ≠ 1 := by decide +kernel
private theorem top_cases (q : Equiv.Perm (Fin 2)) : q = 1 ∨ q = swap := by
  exact (show ∀ q : Equiv.Perm (Fin 2), q = 1 ∨ q = swap from by decide +kernel) q

def quotientSection (q : Equiv.Perm (Fin 2)) : Original :=
  if q = 1 then 1 else originalGenerator 2

private theorem section_one : quotientSection 1 = 1 := by simp [quotientSection]
private theorem section_swap : quotientSection swap = originalGenerator 2 := by
  simp [quotientSection, swap_ne_one]
private theorem section_top (q : Equiv.Perm (Fin 2)) : blockFrame.top (quotientSection q) = q := by
  rcases top_cases q with rfl | rfl
  · simp [section_one]
  · simp [section_swap, top_generator, tops]

theorem top_surjective : Function.Surjective blockFrame.top :=
  fun q => ⟨quotientSection q, section_top q⟩

/-- Index-two Schreier generation retains the genuine square of the swapping
original generator; no involution premise is used. -/
theorem kernelGenerators_generate :
    Subgroup.closure (Set.range kernelGenerators) = ⊤ := by
  let s := schreierKernelGenerators originalGenerator blockFrame.top quotientSection section_top
  have hgen : Subgroup.closure (Set.range s) = ⊤ :=
    schreierKernelGenerators_generate originalGenerator
      (originalGeneratedGenerators_generate generators) blockFrame.top quotientSection section_top section_one
  have hmem (i : Fin 9) : kernelGenerators i ∈ Subgroup.closure (Set.range kernelGenerators) :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hs : swap * swap = 1 := by decide +kernel
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨q,j⟩, rfl⟩
  rcases top_cases q with rfl | rfl
  · fin_cases j
    · convert hmem 0 using 1 <;> apply Subtype.ext <;>
        simp [s, schreierKernelGenerators, schreierWords, section_one,
          section_swap, top_generator, tops, kernelGenerators, rawKernelGenerators]
    · convert hmem 1 using 1 <;> apply Subtype.ext <;>
        simp [s, schreierKernelGenerators, schreierWords, section_one,
          section_swap, top_generator, tops, kernelGenerators, rawKernelGenerators]
    · have he : s (1,2) = 1 := by
        apply Subtype.ext
        simp [s, schreierKernelGenerators, schreierWords, section_one,
          section_swap, top_generator, tops]
      change s (1,2) ∈ Subgroup.closure (Set.range kernelGenerators)
      rw [he]
      exact Subgroup.one_mem _
  · have he : s (swap,j) = kernelGenerators ((![5,6,2] : Fin 3 → Fin 9) j) := by
      apply Subtype.ext
      fin_cases j <;>
        simp [s, schreierKernelGenerators, schreierWords, section_one,
          section_swap, top_generator, tops, kernelGenerators, rawKernelGenerators, hs]
    rw [he]
    exact hmem _

end SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
