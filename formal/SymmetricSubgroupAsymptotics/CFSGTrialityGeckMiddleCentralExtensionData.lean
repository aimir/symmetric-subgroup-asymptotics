import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCentralParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedScalarPairing
import SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorCardinality
import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex

/-! The literal fixed middle radical satisfies the central-extension data
with its actual highest-root homomorphism and its actual commutator.
This packages proved identities rather than a recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCentralExtensionData

open CFSGTrialityGeckDiagramCovariance
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityMiddleFixedTensorCardinality
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleFixedPairingValues
open CFSGTrialityGeckMiddleFixedQuotientCoordinates CFSGTrialityGeckMiddleFixedCentralParameters
open CFSGTrialityGeckMiddleFixedScalarPairing CFSGTrialityGeckMiddleFixedTensorImage
open scoped commutatorElement
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem central_commutator (q : CFSG.PrimePower) (u v : fixedMiddle q) :
    u*v*u⁻¹*v⁻¹ = central q (Multiplicative.ofAdd
      (fixedPairing q (coordinate q u) (coordinate q v))) := by
  obtain ⟨t,ht,hpair⟩ := fixed_middle_pairing_parameter q u v
    (coordinate q u) (coordinate q v) (coordinate_spec q u).symm (coordinate_spec q v).symm
  have ht' : t = fixedPairing q (coordinate q u) (coordinate q v) :=
    Subtype.ext hpair.symm
  apply Subtype.ext
  have he := ht.symm
  rw [ht'] at he
  exact he

def extensionData (q : CFSG.PrimePower) :
    CentralExtensionScalarPairingIndex.Data (F := F q) (V := fullEnvelope q) (N := fixedMiddle q) where
  projection := projection q
  central := central q
  central_injective := central_injective q
  central_range := central_range q
  projection_surjective := projection_surjective q
  pairing := fixedPairing q
  alternating := fixedPairing_alternating q
  full := fixedPairing_full q
  commutator := central_commutator q

theorem fixedMiddle_card (q : CFSG.PrimePower) : Nat.card (fixedMiddle q) = q.order^9 := by
  have he := (extensionData q).card_eq 4 (by rw [fullEnvelope_finrank])
  rw [CFSGTrialityFixedField.fixedField_card] at he
  exact he

theorem central_proper_index (q : CFSG.PrimePower) (L : Subgroup (fixedMiddle q))
    (hL : ¬(central q).range ≤ L) : q.prime*q.order^4 ≤ L.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have he := (extensionData q).index_least q.prime 4
    (by rw [fullEnvelope_finrank]) L hL
  rw [CFSGTrialityFixedField.fixedField_card] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCentralExtensionData
