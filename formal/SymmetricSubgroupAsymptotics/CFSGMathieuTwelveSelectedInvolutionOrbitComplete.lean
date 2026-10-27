import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock00
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock01
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock02
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock03
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock04
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock05
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock06
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock07
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock08
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock09
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock10
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock11
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock12
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock13
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock14
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock15

/-! Assemble the sixteen checked blocks of the same original M12 conjugacy orbit.
All row bindings and transitions are checked exports; no class-size premise is supplied. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitComplete
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open FiniteGeneratedConjugacyOrbitCertificate
open CFSGMathieuTwelveSelectedInvolutionOrbitData

private def blockSize (b : Fin 16) : ℕ := if b.val < 15 then 32 else 15

private def blockIndex (b : Fin 16) (j : Fin (blockSize b)) : Fin 495 :=
  ⟨32*b.val+j.val,by
    have hb : b.val < 16 := b.isLt
    have hj : j.val < (if b.val < 15 then 32 else 15) := j.isLt
    split_ifs at hj <;> omega⟩

/-- Proof fields only: finite case elimination stays in Prop. -/
private structure BlockFacts (b : Fin 16) : Prop where
  row_image : ∀ j p, (rows (blockIndex b j)).val p = rowForward (blockIndex b j) p
  transition_check : ∀ s j p,
    rowForward (nextIndex s (blockIndex b j)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex b j) p)
  code_encoding : ∀ j,
    code (blockIndex b j) = ∑ p : Fin 12, (rowForward (blockIndex b j) p).val * 2^(4*p.val)
  code_adjacent : ∀ j (h : (blockIndex b j).val+1 < 495),
    code (blockIndex b j) < code ⟨(blockIndex b j).val+1,h⟩

private theorem blockFacts (b : Fin 16) : BlockFacts b := by
  fin_cases b <;> dsimp only
  · have hindex (j : Fin 32) :
        blockIndex (⟨0,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock00.blockIndex j := by
      apply Fin.ext
      simp [blockIndex,CFSGMathieuTwelveSelectedInvolutionOrbitBlock00.blockIndex]
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock00.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock00.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock00.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (fun _ => CFSGMathieuTwelveSelectedInvolutionOrbitBlock00.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨1,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock01.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock01.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock01.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock01.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock01.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨2,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock02.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock02.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock02.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock02.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock02.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨3,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock03.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock03.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock03.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock03.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock03.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨4,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock04.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock04.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock04.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock04.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock04.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨5,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock05.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock05.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock05.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock05.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock05.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨6,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock06.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock06.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock06.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock06.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock06.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨7,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock07.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock07.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock07.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock07.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock07.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨8,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock08.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock08.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock08.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock08.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock08.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨9,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock09.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock09.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock09.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock09.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock09.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨10,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock10.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock10.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock10.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock10.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock10.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨11,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock11.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock11.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock11.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock11.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock11.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨12,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock12.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock12.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock12.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock12.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock12.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨13,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock13.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock13.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock13.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock13.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock13.code_adjacent j) }
  · have hindex (j : Fin 32) :
        blockIndex (⟨14,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock14.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock14.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock14.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock14.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock14.code_adjacent j) }
  · have hindex (j : Fin 15) :
        blockIndex (⟨15,by omega⟩ : Fin 16) j = CFSGMathieuTwelveSelectedInvolutionOrbitBlock15.blockIndex j := by
      apply Fin.ext
      rfl
    exact {
      row_image := fun j p => Eq.mpr
        (congrArg (fun z : Fin 495 => (rows z).val p = rowForward z p) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock15.row_image j p)
      transition_check := fun s j p => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          rowForward (nextIndex s z) (generatorPermutation s p) =
            generatorPermutation s (rowForward z p)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock15.transition_check s j p)
      code_encoding := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 =>
          code z = ∑ p : Fin 12, (rowForward z p).val * 2^(4*p.val)) (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock15.code_encoding j)
      code_adjacent := fun j => Eq.mpr
        (congrArg (fun z : Fin 495 => ∀ h : z.val+1 < 495, code z < code ⟨z.val+1,h⟩)
          (hindex j))
        (CFSGMathieuTwelveSelectedInvolutionOrbitBlock15.code_adjacent j) }

private def selectedBlock (i : Fin 495) : Fin 16 :=
  ⟨i.val/32,by have hi : i.val < 495 := i.isLt; omega⟩

private def selectedLocal (i : Fin 495) : Fin (blockSize (selectedBlock i)) :=
  ⟨i.val%32,by
    have hi : i.val < 495 := i.isLt
    change i.val%32 < (if i.val/32 < 15 then 32 else 15)
    split_ifs with h
    · exact Nat.mod_lt _ (by omega)
    · omega⟩

private theorem selected_index (i : Fin 495) :
    blockIndex (selectedBlock i) (selectedLocal i) = i := by
  apply Fin.ext
  change 32*(i.val/32)+i.val%32 = i.val
  omega

theorem row_image (i : Fin 495) (p : Fin 12) :
    (rows i).val p = rowForward i p := by
  have h := (blockFacts (selectedBlock i)).row_image (selectedLocal i) p
  simpa only [selected_index] using h

theorem transition_check (s : Fin 4) (i : Fin 495) (p : Fin 12) :
    rowForward (nextIndex s i) (generatorPermutation s p) =
      generatorPermutation s (rowForward i p) := by
  have h := (blockFacts (selectedBlock i)).transition_check s (selectedLocal i) p
  simpa only [selected_index] using h

theorem code_encoding (i : Fin 495) :
    code i = ∑ p : Fin 12, (rowForward i p).val * 2^(4*p.val) := by
  have h := (blockFacts (selectedBlock i)).code_encoding (selectedLocal i)
  simpa only [selected_index] using h

private theorem code_adjacent (i : Fin 495) :
    ∀ hi : i.val+1 < 495, code i < code ⟨i.val+1,hi⟩ :=
  Eq.mp
    (congrArg (fun z : Fin 495 => ∀ hi : z.val+1 < 495, code z < code ⟨z.val+1,hi⟩)
      (selected_index i))
    ((blockFacts (selectedBlock i)).code_adjacent (selectedLocal i))

theorem code_strictMono : StrictMono code := by
  apply (Fin.strictMono_iff_lt_succ (n := 494)).mpr
  intro i
  have hi : i.val < 494 := i.isLt
  exact code_adjacent i.castSucc (by change i.val+1 < 495; omega)

theorem rows_injective : Function.Injective rows := by
  intro i j hij
  apply code_strictMono.injective
  rw [code_encoding i,code_encoding j]
  apply Finset.sum_congr rfl
  intro p _
  have hp := congrArg (fun z : M12 => (z.val p).val) hij
  simpa only [row_image] using congrArg (fun n : ℕ => n*2^(4*p.val)) hp

def certificate : Certificate x y x rows where
  base := 358
  base_eq := by
    have hword : originWords[(358 : Fin 495).val]! = [] := by decide +kernel
    simp only [rows,conjugator,hword,SignedPermutationWordPointEvaluation.eval,
      one_mul,inv_one,mul_one]
  conjugator := conjugator
  origins := fun _ => rfl
  nextIndex := nextIndex
  transitions := by
    intro s i
    apply eq_mul_inv_iff_mul_eq.mpr
    apply Subtype.ext
    apply Equiv.ext
    intro p
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,row_image,generator_coe]
      using transition_check s i p

theorem selected_class_card : Nat.card {g : M12 // IsConj g x} = 495 :=
  FiniteGeneratedConjugacyOrbitCertificate.class_card_eq certificate
    CFSGMathieuTwelveConjugacyOrbitGenerators.original_pair_generates rows_injective

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitComplete
