import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! A quantitative consequence of actual scalar-normalizer reconstruction.
The normalizer embeds into units times literal field automorphisms. No
identification of these groups with simple-group outer automorphisms occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
variable (K : Type*) [Field K]

def normalizerParameters
    (A : Subgroup.normalizer (scalarSubgroup K : Set (AddAut K))) : Kˣ×(K ≃+* K) :=
  (Units.mk0 (A.val 1) (additive_one_ne_zero A.val),normalizedRingAut A.val A.property)

theorem normalizerParameters_injective : Function.Injective (normalizerParameters K) := by
  intro A B he
  apply Subtype.ext
  apply AddEquiv.ext
  intro x
  have hc := congrArg (fun p : Kˣ×(K ≃+* K) => (p.1 : K)) he
  have hσ := congrArg (fun p : Kˣ×(K ≃+* K) => p.2 x) he
  change A.val 1=B.val 1 at hc
  change normalizedRingAut A.val A.property x=normalizedRingAut B.val B.property x at hσ
  calc
    A.val x=A.val 1*normalizedRingAut A.val A.property x :=
      scalar_times_normalizedRingAut A.val A.property x
    _=B.val 1*normalizedRingAut B.val B.property x := congrArg₂ (fun a b : K => a*b) hc hσ
    _=B.val x := (scalar_times_normalizedRingAut B.val B.property x).symm

variable [Finite K]

theorem card_scalarNormalizer_le :
    Nat.card (Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)))≤
      Nat.card Kˣ*Nat.card (K ≃+* K) := by
  letI scalarNormalizerCard_finiteRingAut : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K→K)) DFunLike.coe_injective
  have he := Nat.card_le_card_of_injective (normalizerParameters K) (normalizerParameters_injective K)
  simpa only [Nat.card_prod] using he

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
