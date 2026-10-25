import SymmetricSubgroupAsymptotics.QuaternaryPauliUnitaryRepresentation
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots
import Mathlib.FieldTheory.Finite.GaloisField

/-! The actual quadratic fixture is transported to the ACTUAL extension
field of an order-two prime power. Squaring agrees with its defining
field automorphism, so the SAME unitary matrices remain unitary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuaternaryUnitaryFieldTransport
open BinaryQuadraticField CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

private instance (q : CFSG.PrimePower) : Fintype (q.Extension 2) := Fintype.ofFinite _

def fieldEquiv (q : CFSG.PrimePower) (hq : q.order=2) : Scalar ≃+* q.Extension 2 :=
  FiniteField.ringEquivOfCardEq (by
    have hc : Nat.card Scalar=Nat.card (q.Extension 2) := by
      rw [extension_two_card,hq]
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    simpa only [Nat.card_eq_fintype_card] using hc)

theorem automorphism_compatibility (q : CFSG.PrimePower) (hq : q.order=2) (z : Scalar) :
    definingFieldAutomorphism q 2 (fieldEquiv q hq z)=
      fieldEquiv q hq (QuaternaryUnitarySymplecticEmbedding.squaring z) := by
  change (fieldEquiv q hq z)^q.order=fieldEquiv q hq (z^2)
  rw [hq,map_pow]

variable (I : Type*) [Fintype I] [DecidableEq I]

def hom (q : CFSG.PrimePower) (hq : q.order=2) :
    QuaternaryUnitarySymplecticEmbedding.unitary I →* (Matrix I I (q.Extension 2))ˣ :=
  (Matrix.GeneralLinearGroup.map (fieldEquiv q hq).toRingHom).comp
    (QuaternaryUnitarySymplecticEmbedding.unitary I).subtype

theorem hom_injective (q : CFSG.PrimePower) (hq : q.order=2) :
    Function.Injective (hom I q hq) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  funext i j
  apply (fieldEquiv q hq).injective
  exact congrArg (fun C : (Matrix I I (q.Extension 2))ˣ => C.val i j) h

theorem preserves_identity_form (q : CFSG.PrimePower) (hq : q.order=2)
    (A : QuaternaryUnitarySymplecticEmbedding.unitary I) :
    (((hom I q hq A).val).map (definingFieldAutomorphism q 2)).transpose*
      (hom I q hq A).val=1 := by
  let f : Matrix I I Scalar →+* Matrix I I (q.Extension 2) :=
    (fieldEquiv q hq).toRingHom.mapMatrix
  have hadj : (((hom I q hq A).val).map (definingFieldAutomorphism q 2)).transpose=
      f (QuaternaryUnitarySymplecticEmbedding.adjoint I A.val.val) := by
    funext i j
    exact automorphism_compatibility q hq (A.val.val j i)
  rw [hadj]
  change f (QuaternaryUnitarySymplecticEmbedding.adjoint I A.val.val)*f A.val.val=1
  rw [←map_mul,A.property,map_one]

end SymmetricSubgroupAsymptotics.QuaternaryUnitaryFieldTransport
