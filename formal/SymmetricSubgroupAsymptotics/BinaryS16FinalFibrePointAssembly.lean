import SymmetricSubgroupAsymptotics.BinaryS16FixedLiteralNaturality

/-!
# Native point assembly for the direct S16 fibre reflection

The imported theorem assembles every routed literal cell on the fixed source
labels.  This module cancels the two exact parameter casts and supplies the
native point square used by the ambient embedding.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FinalFibrePointAssembly

/-- Two opaque native charts commute whenever both return to a common fixed
chart and the fixed charts commute. -/
private theorem transportSquareOfFixed
    {A B X Y Z : Type*}
    (r : A ≃ B) (wA : A ≃ Y) (wB : B ≃ Z)
    (fA : A ≃ X) (fB : B ≃ X)
    (pA : Y ≃ X) (pB : Z ≃ X) (d : Y ≃ Z)
    (hwA : wA.trans pA = fA) (hwB : wB.trans pB = fB)
    (hr : r.trans fB = fA) (hd : pA.trans pB.symm = d) :
    wA.trans d = r.trans wB := by
  apply Equiv.ext
  intro x
  apply pB.injective
  have hdx := Equiv.congr_fun hd (wA x)
  have hAx := Equiv.congr_fun hwA x
  have hBx := Equiv.congr_fun hwB (r x)
  have hrx := Equiv.congr_fun hr x
  simp only [Equiv.trans_apply] at hdx hAx hBx hrx ⊢
  calc
    pB (d (wA x)) = pA (wA x) := by rw [← hdx, pB.apply_symm_apply]
    _ = fA x := hAx
    _ = fB (r x) := hrx.symm
    _ = pB (wB (r x)) := hBx.symm

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierFusionEmbeddingFormula
open BinaryCarrierWordClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FinalFibreReflection
open BinaryS16FixedLiteralNaturality
open BinaryS16FusionNaturalPointChart

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)
abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

section Matched

variable {H K : Actual C}
variable (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
  BinaryS16DirectPhysicalEncoding.blocks C K)
variable (htarget : targetSubgroup C H = targetSubgroup C K)

/-- Stable outer shape of the ambient parameter transport. -/
theorem wordAmbientPointEquiv_eq :
    wordAmbientPointEquiv (H := H) (K := K) C =
      (parameterCast C H).trans (parameterCast C K).symm := rfl

/-- The complete displayed-point assembly commutes with the raw ambient
cast.  This is the final fibre point square. -/
theorem wordLiteralPointChart_natural :
    (BinaryS16DirectPhysicalTarget.wordLiteralPointChart C H).trans
        (wordAmbientPointEquiv (H := H) (K := K) C) =
      (routedLiteralPointEquiv C hblocks htarget).trans
        (BinaryS16DirectPhysicalTarget.wordLiteralPointChart C K) := by
  exact transportSquareOfFixed
    (routedLiteralPointEquiv C hblocks htarget)
    (BinaryS16DirectPhysicalTarget.wordLiteralPointChart C H)
    (BinaryS16DirectPhysicalTarget.wordLiteralPointChart C K)
    (BinaryS16DirectPhysicalTarget.fixedLiteralPointChart C H)
    (BinaryS16DirectPhysicalTarget.fixedLiteralPointChart C K)
    (parameterCast C H) (parameterCast C K)
    (wordAmbientPointEquiv (H := H) (K := K) C)
    (BinaryS16DirectPhysicalTarget.wordLiteralPointChart_trans_parameterCast C H)
    (BinaryS16DirectPhysicalTarget.wordLiteralPointChart_trans_parameterCast C K)
    (BinaryS16FixedLiteralNaturality.fixedLiteralPointChart_natural
      C hblocks htarget)
    (wordAmbientPointEquiv_eq C)

end Matched

end SymmetricSubgroupAsymptotics.BinaryS16FinalFibrePointAssembly

end
