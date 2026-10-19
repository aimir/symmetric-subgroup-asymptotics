import SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
import SymmetricSubgroupAsymptotics.SchreierKernelSubtypeGenerators
import SymmetricSubgroupAsymptotics.IndexTwoSchreier
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Exact original twelve-point row182 block kernel. The two components
are related by the checked word graph, not ordinary point conjugacy.
This file does not supply a socle bound or alter an original denominator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

abbrev Original := Row182Top
abbrev generators := row182Generators

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
  ![originalGenerator 0, originalGenerator 1, 1,
    (originalGenerator 0)⁻¹, (originalGenerator 1)⁻¹,
    originalGenerator 2 * originalGenerator 0 * (originalGenerator 2)⁻¹,
    originalGenerator 2 * originalGenerator 1 * (originalGenerator 2)⁻¹,
    originalGenerator 2 * (originalGenerator 0)⁻¹ * (originalGenerator 2)⁻¹,
    originalGenerator 2 * (originalGenerator 1)⁻¹ * (originalGenerator 2)⁻¹]

private theorem top_raw : ∀ j, blockFrame.top (rawKernelGenerators j) = 1 := by
  intro j
  fin_cases j <;> simp [rawKernelGenerators, map_mul, map_inv, top_generator, tops]

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

private theorem swap_square : originalGenerator 2 * originalGenerator 2 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  decide +kernel

private theorem schreier_one (j : Fin 3) :
    schreierWords originalGenerator blockFrame.top quotientSection (1,j) =
      rawKernelGenerators ((![0,1,2] : Fin 3 → Fin 9) j) := by
  fin_cases j <;>
    simp [schreierWords, section_one, section_swap, top_generator, tops,
      rawKernelGenerators]

private theorem schreier_swap (j : Fin 3) :
    schreierWords originalGenerator blockFrame.top quotientSection (swap,j) =
      rawKernelGenerators ((![5,6,2] : Fin 3 → Fin 9) j) := by
  have hs : swap * swap = 1 := by decide +kernel
  fin_cases j <;>
    simp [schreierWords, section_one, section_swap, top_generator, tops,
      rawKernelGenerators, hs, swap_square]

/-- The nine selected words generate the exact original top kernel. -/
theorem kernelGenerators_generate :
    Subgroup.closure (Set.range kernelGenerators) = ⊤ := by
  let s := schreierKernelGenerators originalGenerator blockFrame.top quotientSection section_top
  have hgen : Subgroup.closure (Set.range s) = ⊤ :=
    schreierKernelGenerators_generate originalGenerator
      (originalGeneratedGenerators_generate generators) blockFrame.top quotientSection section_top section_one
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨q,j⟩, rfl⟩
  rcases top_cases q with rfl | rfl
  · have he : s (1,j) = kernelGenerators ((![0,1,2] : Fin 3 → Fin 9) j) :=
      Subtype.ext (schreier_one j)
    rw [he]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  · have he : s (swap,j) = kernelGenerators ((![5,6,2] : Fin 3 → Fin 9) j) :=
      Subtype.ext (schreier_swap j)
    rw [he]
    exact Subgroup.subset_closure (Set.mem_range_self _)

theorem coordinate_zero_checked : ∀ (j : Fin 9) (x : Fin 6),
    blockFrame.kernelCoordinate 0 (kernelGenerators j) x =
      Row182QuotientWordGraph.sourceGenerators j x := by
  decide +kernel

theorem coordinate_one_checked : ∀ (j : Fin 9) (x : Fin 6),
    blockFrame.kernelCoordinate 1 (kernelGenerators j) x =
      Row182QuotientWordGraph.targetGenerators j x := by
  decide +kernel

/-- Faithfulness of the first component on the original block kernel. -/
theorem coordinate_zero_injective : Function.Injective (blockFrame.kernelCoordinate 0) := by
  apply Row182QuotientWordGraph.certificate.first_comp_injective_of_generated
    blockFrame.twoKernelMap blockFrame.twoKernelMap_injective kernelGenerators kernelGenerators_generate
  intro j
  exact Prod.ext (Equiv.ext (coordinate_zero_checked j))
    (Equiv.ext (coordinate_one_checked j))

end SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel
