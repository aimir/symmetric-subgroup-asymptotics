import SymmetricSubgroupAsymptotics.LinearRepresentationSelectedPrimePeriod
import SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatrixCertificates

/-! Exact positive-word transport from the ORIGINAL pinned J1 model.
The selected word is x*y*x*y^2; no whole-word order or image/model
identification is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGJankoOneCommwordLinearBinding
open CFSGJankoOnePresentationGenerators CFSGJankoOneLiteralRepresentation
open CFSGJankoOneSevenMatrices
abbrev V := Fin 7 → ZMod 11
abbrev Model := CFSG.Models.Presentations.J1.Model
abbrev ρ : Model →* MatrixImage := matrixRepresentation relatorPacket

def selectedWord : Model := pinnedX*pinnedY*pinnedX*pinnedY^2

def firstEnd : Module.End (ZMod 11) V := Matrix.mulVecLin matrixA
def secondEnd : Module.End (ZMod 11) V := Matrix.mulVecLin matrixB
def wordEnd : Module.End (ZMod 11) V := firstEnd*secondEnd*firstEnd*secondEnd^2

theorem first_binding : LinearRepresentationSelectedPrimePeriod.linearEnd ρ pinnedX=firstEnd := by
  apply LinearMap.ext
  intro v
  rw [LinearRepresentationSelectedPrimePeriod.end_apply]
  change (representation relatorPacket pinnedX : M) *ᵥ v=matrixA *ᵥ v
  rw [representation_pinnedX]
  rfl

theorem second_binding : LinearRepresentationSelectedPrimePeriod.linearEnd ρ pinnedY=secondEnd := by
  apply LinearMap.ext
  intro v
  rw [LinearRepresentationSelectedPrimePeriod.end_apply]
  change (representation relatorPacket pinnedY : M) *ᵥ v=matrixB *ᵥ v
  rw [representation_pinnedY]
  rfl

theorem word_binding : LinearRepresentationSelectedPrimePeriod.linearEnd ρ selectedWord=wordEnd := by
  simp only [selectedWord,map_mul,map_pow,first_binding,second_binding,wordEnd]

theorem wordEnd_apply (v : V) : wordEnd v=
    matrixA *ᵥ (matrixB *ᵥ (matrixA *ᵥ (matrixB *ᵥ (matrixB *ᵥ v)))) := by
  simp only [wordEnd,pow_two,Module.End.mul_apply,firstEnd,secondEnd,Matrix.mulVecLin_apply]

end SymmetricSubgroupAsymptotics.CFSGJankoOneCommwordLinearBinding
