import SymmetricSubgroupAsymptotics.Selected1542OriginalKernels
import SymmetricSubgroupAsymptotics.FiniteKernelIndexedSignature

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
local instance : Fintype originalPreimage := Fintype.ofFinite _

def originalCode (g : Original) : ℕ := pointCode g.val

def indexedSignature (g : Original) : ℕ :=
  (Finset.univ.image (fun i : Fin 64 => pointCode (g.val*preimageElements i))).min'
    (by exact Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem actual_signature_eq (g : Original) :
    FiniteKernelCosetSignature.signature originalPreimage.subtype originalCode g=indexedSignature g := by
  have he := FiniteKernelCosetSignature.codes_eq_indexed originalPreimage.subtype originalCode
    preimageTable.chart preimageTable.chart_surjective g
  have he' : FiniteKernelCosetSignature.codes originalPreimage.subtype originalCode g=
      Finset.univ.image (fun i : Fin 64 => pointCode (g.val*preimageElements i)) := he
  unfold FiniteKernelCosetSignature.signature indexedSignature
  simp only [he']

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
