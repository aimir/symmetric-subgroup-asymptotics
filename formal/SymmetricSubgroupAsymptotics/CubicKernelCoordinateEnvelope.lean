import SymmetricSubgroupAsymptotics.CubicKernelNonzeroHead
import SymmetricSubgroupAsymptotics.CubicZeroScalarKernelEnvelope
import SymmetricSubgroupAsymptotics.ScalarFourDoubleHeadB6Envelope
import SymmetricSubgroupAsymptotics.OriginalKernelQuotientChart

/-! Actual cubic kernel coordinates yield the B6 envelope in both cases:
a surviving scalar coordinate uses the joint trace count; no scalar
coordinate leaves an actual central binary kernel and the KP cube-map route. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicKernelCoordinateEnvelope

variable {Q : Type} [Group Q] [Finite Q]
  (top : Q →* CyclicThree) (htop : Function.Surjective top)
  (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)
  (D : CubicBinaryCoordinates A.ρ)

/-- Exact original conjugation expressed in the inverse kernel chart. -/
theorem inverseChart_conjugate (q : Q) (p : top.ker) :
    E.equiv.symm (MulAut.conjNormal q p) =
      Multiplicative.ofAdd (A.ρ (top q) (Multiplicative.toAdd (E.equiv.symm p))) := by
  apply E.equiv.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  change q*(p : Q)*q⁻¹ = _
  simpa only [ofAdd_toAdd,MulEquiv.apply_symm_apply] using
    (E.conjugate q (Multiplicative.toAdd (E.equiv.symm p))).symm

include A E in
omit [Finite Q] in
theorem kernel_exponent (p : top.ker) : p^2=1 := by
  apply E.equiv.symm.injective
  rw [map_pow,map_one]
  change (Multiplicative.ofAdd (Multiplicative.toAdd (E.equiv.symm p)))^2=1
  rw [← ofAdd_nsmul,ZModModule.char_nsmul_eq_zero]
  rfl

/-- No scalar source bound is an input: both branches follow from the
same actual coordinate chart and existing explicit KP literature input. -/
def certificate (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6QuotientCertificate Q := by
  let s := CubicElementaryKernelCoordinates.scalar top A.ρ E.equiv.symm D
  let a := CubicElementaryKernelCoordinates.invariant top A.ρ E.equiv.symm D
  have hconj := inverseChart_conjugate top A E
  by_cases hs : ∃ j : Fin 2, ∃ p : top.ker, s j p ≠ 1
  · let j := Classical.choose hs
    have hj := Classical.choose_spec hs
    exact (CubicKernelNonzeroHead.jointData top htop A.ρ E.equiv.symm D hconj j hj).b6Certificate
  · have hzero : ∀ j p, s j p=1 := by
      intro j p
      by_contra hn
      exact hs ⟨j,p,hn⟩
    have hjoint : Function.Injective (fun p : top.ker => (a 0 p,a 1 p)) := by
      intro p q he
      apply CubicElementaryKernelCoordinates.joint top A.ρ E.equiv.symm D
      exact Prod.ext he (Prod.ext ((hzero 0 p).trans (hzero 0 q).symm)
        ((hzero 1 p).trans (hzero 1 q).symm))
    exact CubicZeroScalarKernelEnvelope.certificate top a hjoint
      (CubicElementaryKernelCoordinates.invariant_conj top A.ρ E.equiv.symm D hconj)
      (kernel_exponent top A E) hKP

end CubicKernelCoordinateEnvelope
end SymmetricSubgroupAsymptotics
end
