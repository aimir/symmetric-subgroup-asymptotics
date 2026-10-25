import SymmetricSubgroupAsymptotics.QuaternaryUnitaryFieldTransport
import SymmetricSubgroupAsymptotics.HermitianDeterminantCorrection
import SymmetricSubgroupAsymptotics.CharTwoHyperbolicOrthonormalBridge
import SymmetricSubgroupAsymptotics.CFSGSpecialLinearReindex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalForm
import SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeProjectiveKernel

/-! A faithful hom from the SAME displayed three-dimensional F4 unitary
source into the ORIGINAL rank-three order-two unitary model. Determinant
correction, the literal signed-form change of basis and the full actual
projective cover are all retained; no GU order or splitting is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreePauliEmbedding
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates CFSGSerreOrdinaryTwists
private abbrev P := ZMod 3
private abbrev Source := QuaternaryUnitarySymplecticEmbedding.unitary P

private def index : P ⊕ Unit ≃ Fin 4 := Fintype.equivOfCardEq (by decide)

private def traceParameter (q : CFSG.PrimePower) : q.Extension 2 :=
  Classical.choose (CFSGTwistedAQuadraticTrace.exists_trace_eq_fixed q 1 (map_one _))

private theorem traceParameter_spec (q : CFSG.PrimePower) :
    definingFieldAutomorphism q 2 (traceParameter q)+traceParameter q=1 := by
  simpa only [add_comm] using Classical.choose_spec
    (CFSGTwistedAQuadraticTrace.exists_trace_eq_fixed q 1 (map_one _))

private def corrected (q : CFSG.PrimePower) (hq : q.order=2) :
    Source →* Matrix.SpecialLinearGroup (Fin 4) (q.Extension 2) :=
  (CFSGSpecialLinearReindex.reindexHom index).comp
    (HermitianDeterminantCorrection.hom.comp (QuaternaryUnitaryFieldTransport.hom P q hq))

private theorem corrected_injective (q : CFSG.PrimePower) (hq : q.order=2) :
    Function.Injective (corrected q hq) := by
  intro A B h
  apply QuaternaryUnitaryFieldTransport.hom_injective P q hq
  apply HermitianDeterminantCorrection.hom_injective
  apply Subtype.ext
  have he := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 4) (q.Extension 2) => C.val) h
  exact (Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2) index).injective he

private theorem corrected_isometric (q : CFSG.PrimePower) (hq : q.order=2) (A : Source) :
    (((corrected q hq A).val).map (definingFieldAutomorphism q 2)).transpose*
      (corrected q hq A).val=1 := by
  let B := HermitianDeterminantCorrection.hom (QuaternaryUnitaryFieldTransport.hom P q hq A)
  have hB := HermitianDeterminantCorrection.preserves_identity_form
    (definingFieldAutomorphism q 2) (QuaternaryUnitaryFieldTransport.hom P q hq A)
    (QuaternaryUnitaryFieldTransport.preserves_identity_form P q hq A)
  have hh := reindex_isometry index (definingFieldAutomorphism q 2).toRingHom
    (1 : Matrix (P ⊕ Unit) (P ⊕ Unit) (q.Extension 2)) B.val
    (by simpa only [Matrix.mul_one] using hB)
  have h1 : Matrix.reindex index index (1 : Matrix (P ⊕ Unit) (P ⊕ Unit) (q.Extension 2))=1 :=
    (Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2) index).map_one
  simpa only [h1,Matrix.mul_one] using hh

private def signedHom (q : CFSG.PrimePower) (hq : q.order=2) :
    Source →* (Matrix (Fin 4) (Fin 4) (q.Extension 2))ˣ :=
  (MulAut.conj (CharTwoHyperbolicOrthonormalBridge.basisUnit (traceParameter q))).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toGL.comp (corrected q hq))

private theorem signedHom_injective (q : CFSG.PrimePower) (hq : q.order=2) :
    Function.Injective (signedHom q hq) :=
  (MulAut.conj (CharTwoHyperbolicOrthonormalBridge.basisUnit (traceParameter q))).injective.comp
    (Matrix.SpecialLinearGroup.toGL_injective.comp (corrected_injective q hq))

private theorem signedHom_det (q : CFSG.PrimePower) (hq : q.order=2) (A : Source) :
    Matrix.det (signedHom q hq A).val=1 := by
  have hh : Matrix.GeneralLinearGroup.det (signedHom q hq A)=1 := by
    change Matrix.GeneralLinearGroup.det
      (CharTwoHyperbolicOrthonormalBridge.basisUnit (traceParameter q)*
        Matrix.SpecialLinearGroup.toGL (corrected q hq A)*
          (CharTwoHyperbolicOrthonormalBridge.basisUnit (traceParameter q))⁻¹)=1
    rw [map_mul,map_mul,map_inv,Matrix.SpecialLinearGroup.coeToGL_det,mul_one,mul_inv_cancel]
  exact congrArg Units.val hh

private def adjoint {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K ≃+* K) (M : Matrix I I K) := (sigma.toRingHom.mapMatrix M).transpose

private theorem adjoint_mul {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K ≃+* K) (A B : Matrix I I K) :
    adjoint sigma (A*B)=adjoint sigma B*adjoint sigma A := by
  simp only [adjoint,map_mul,Matrix.transpose_mul]

private theorem conjugate_isometric {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K ≃+* K) (H : Matrix I I K) (C A : (Matrix I I K)ˣ)
    (hC : adjoint sigma C.val*H*C.val=1)
    (hA : adjoint sigma A.val*A.val=1) :
    adjoint sigma (C*A*C⁻¹).val*H*(C*A*C⁻¹).val=H := by
  have hcinv : C.val*(C⁻¹).val=1 :=
    congrArg (fun U : (Matrix I I K)ˣ => U.val) (mul_inv_cancel C)
  have hcancel : adjoint sigma (C⁻¹).val*adjoint sigma C.val=1 := by
    rw [←adjoint_mul]
    change adjoint sigma (C.val*(C⁻¹).val)=1
    rw [hcinv]
    simp only [adjoint,map_one,Matrix.transpose_one]
  have hH : adjoint sigma (C⁻¹).val*(C⁻¹).val=H := by
    calc
      _=adjoint sigma (C⁻¹).val*(adjoint sigma C.val*H*C.val)*(C⁻¹).val := by
        rw [hC,Matrix.mul_one]
      _=(adjoint sigma (C⁻¹).val*adjoint sigma C.val)*H*(C.val*(C⁻¹).val) := by
        simp only [Matrix.mul_assoc]
      _=H := by rw [hcancel,hcinv,Matrix.one_mul,Matrix.mul_one]
  change adjoint sigma (C.val*A.val*(C⁻¹).val)*H*(C.val*A.val*(C⁻¹).val)=H
  rw [adjoint_mul,adjoint_mul]
  calc
    _=adjoint sigma (C⁻¹).val*(adjoint sigma A.val*(adjoint sigma C.val*H*C.val)*A.val)*
        (C⁻¹).val := by simp only [Matrix.mul_assoc]
    _=adjoint sigma (C⁻¹).val*(adjoint sigma A.val*A.val)*(C⁻¹).val := by
      rw [hC,Matrix.mul_one]
    _=adjoint sigma (C⁻¹).val*(C⁻¹).val := by rw [hA,Matrix.mul_one]
    _=H := hH

private theorem signedHom_isometric (q : CFSG.PrimePower) (hq : q.order=2) (A : Source) :
    (((signedHom q hq A).val).map (definingFieldAutomorphism q 2)).transpose*
      (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3)*
        (signedHom q hq A).val=(signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3) := by
  have hp : q.prime=2 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
      (by decide : (1:ℕ)≠0) (show q.prime^q.exponent=2^1 from hq)
  letI : CharP (q.Extension 2) 2 := by rw [←hp.1]; infer_instance
  exact conjugate_isometric (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 3)
    (CharTwoHyperbolicOrthonormalBridge.basisUnit (traceParameter q))
    (Matrix.SpecialLinearGroup.toGL (corrected q hq A))
    (CharTwoHyperbolicOrthonormalBridge.pullback_signed_reversal _ _ (traceParameter_spec q))
    (corrected_isometric q hq A)

private theorem signedHom_fixed (q : CFSG.PrimePower) (hq : q.order=2) (A : Source) :
    diagramFieldUnitHom (q.Extension 2) 3 (definingFieldAutomorphism q 2).toRingHom
      (signedHom q hq A)=signedHom q hq A :=
  unit_fixed_of_signedForm (q.Extension 2) 3 (definingFieldAutomorphism q 2).toRingHom
    (signedHom q hq A) (signedHom_isometric q hq A)

/-- Construct the actual nested subgroups with an ABSTRACT source hom.
This keeps concrete corrected matrices out of membership elaboration. -/
private def fixedLift {G : Type*} [Group G] (q : CFSG.PrimePower) (r : ℕ)
    (f : G →* (Mat (q.Extension 2) r)ˣ)
    (hdet : ∀ g, Matrix.det (f g).val=1)
    (hfixed : ∀ g, diagramFieldUnitHom (q.Extension 2) r
      (definingFieldAutomorphism q 2).toRingHom (f g)=f g) :
    G →* naturalFixed r q where
  toFun g := ⟨⟨f g,unit_mem_natural_of_det (q.Extension 2) r (f g) (hdet g)⟩,hfixed g⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one f
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; exact map_mul f g h

/-- The SAME source matrices, now in the actual natural fixed subgroup. -/
def naturalHom (q : CFSG.PrimePower) (hq : q.order=2) : Source →* naturalFixed 3 q :=
  fixedLift q 3 (signedHom q hq) (signedHom_det q hq) (signedHom_fixed q hq)

theorem naturalHom_injective (q : CFSG.PrimePower) (hq : q.order=2) :
    Function.Injective (naturalHom q hq) := by
  intro A B h
  exact signedHom_injective q hq
    (congrArg (fun C : naturalFixed 3 q => C.val.val) h)

/-- The full original projective model, not an assumed SU recognition. -/
def hom (q : CFSG.PrimePower) (hq : q.order=2) : Source →* CFSG.Models.TwistedA 3 q :=
  (unitaryProjectiveCover q 0).comp (naturalHom q hq)

theorem hom_injective (q : CFSG.PrimePower) (hq : q.order=2) :
    Function.Injective (hom q hq) := by
  have hkernel := CFSGUnitaryCoprimeProjectiveKernel.unitaryProjectiveCover_kernel_card_eq_one
    q 0 (by norm_num [hq])
  have hcover := (unitaryProjectiveCover q 0).ker_eq_bot_iff.mp
    ((unitaryProjectiveCover q 0).ker.eq_bot_of_card_eq hkernel)
  exact hcover.comp (naturalHom_injective q hq)

end SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreePauliEmbedding
