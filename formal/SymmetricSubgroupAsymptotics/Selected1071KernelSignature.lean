import SymmetricSubgroupAsymptotics.Selected1071OriginalKernel
import SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature

/-! The generic actual-kernel signature is exactly the four-term signature
in the selected original-coordinate receipts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

local instance : Fintype originalKernel := Fintype.ofFinite _

def originalCode (g : Original) : ℕ := pointCode g.val

def originalFourSignature (g : Original) : ℕ :=
  min (pointCode (g.val*kernelElements 0))
    (min (pointCode (g.val*kernelElements 1))
      (min (pointCode (g.val*kernelElements 2)) (pointCode (g.val*kernelElements 3))))

theorem actual_signature_eq (g : Original) :
    FiniteKernelCosetSignature.signature originalKernel.subtype originalCode g=
      originalFourSignature g := by
  apply le_antisymm
  · have h (i : Fin 4) :
        FiniteKernelCosetSignature.signature originalKernel.subtype originalCode g ≤
          pointCode (g.val*kernelElements i) := by
      unfold FiniteKernelCosetSignature.signature
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨kernelElement i,Finset.mem_univ _,rfl⟩
    exact le_min (h 0) (le_min (h 1) (le_min (h 2) (h 3)))
  · unfold FiniteKernelCosetSignature.signature
    apply Finset.le_min'
    intro n hn
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨i,rfl⟩ := kernelElement_surjective r
    change originalFourSignature g ≤ pointCode (g.val*kernelElements i)
    unfold originalFourSignature
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
