import SymmetricSubgroupAsymptotics.CFSGUnitaryProjectiveSimilitudeCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralPointFaithful
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation

/-! Counting after actual unitary geometric reconstruction. The
geometric factorization is an explicit premise of this intermediate
consumer, not an asserted reconstruction theorem or a new T1 endpoint.
Only the field factor and projective similitude IMAGE are charged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup CFSGProjectiveFieldAction PrimitiveSocleRawStructure

local instance (q : CFSG.PrimePower) (r : ℕ) :
    Finite ((Fin (r + 1) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (r + 1) → q.Extension 2)) :=
  Finite.of_injective (fun L : (Fin (r + 1) → q.Extension 2) ≃ₗ[q.Extension 2]
    (Fin (r + 1) → q.Extension 2) => (L : (Fin (r + 1) → q.Extension 2) → Fin (r + 1) → q.Extension 2))
    DFunLike.coe_injective
local instance (q : CFSG.PrimePower) : Finite (q.Extension 2 ≃+* q.Extension 2) :=
  Finite.of_injective (fun tau : q.Extension 2 ≃+* q.Extension 2 =>
    (tau : q.Extension 2 → q.Extension 2)) DFunLike.coe_injective
local instance (q : CFSG.PrimePower) (tau : q.Extension 2 ≃+* q.Extension 2) :
    RingHomSurjective tau.toRingHom := ⟨tau.surjective⟩
local instance (q : CFSG.PrimePower) (tau : q.Extension 2 ≃+* q.Extension 2) :
    RingHomInvPair tau.toRingHom tau.symm.toRingHom := RingHomInvPair.of_ringEquiv tau
local instance (q : CFSG.PrimePower) (tau : q.Extension 2 ≃+* q.Extension 2) :
    RingHomInvPair tau.symm.toRingHom tau.toRingHom := RingHomInvPair.of_ringEquiv_symm tau

theorem quadraticExtension_card_ringAut (q : CFSG.PrimePower) :
    Nat.card (q.Extension 2 ≃+* q.Extension 2) = 2 * q.exponent := by
  let q₂ : CFSG.PrimePower := ⟨q.prime,2 * q.exponent,q.prime_isPrime,
    Nat.mul_pos (by omega) q.exponent_pos⟩
  exact CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q₂

theorem unitary_card_aut_le_of_field_linear_factor (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)]
    (hfactor : ∀ f : MulAut (CFSG.Models.TwistedA (s + 3) q),
      ∃ (tau : q.Extension 2 ≃+* q.Extension 2)
        (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s + 3))),
        ∀ P : SingularPoint (definingFieldAutomorphism q 2)
          (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
        ((unitaryOrthogonalityActionHom q s f).val P).val =
          (P.val.map g.val.toLinearMap).map (coordinateEquiv tau).toLinearMap) :
    Nat.card (MulAut (CFSG.Models.TwistedA (s + 3) q)) ≤
      (2 * q.exponent) * Nat.card (CFSGTwistedAUpperUnipotent.naturalFixed (s + 3) q) := by
  classical
  let sigma := definingFieldAutomorphism q 2
  let H := signedReversalUnit (q.Extension 2) (s + 3)
  choose tau g hpoints using hfactor
  let encode : MulAut (CFSG.Models.TwistedA (s + 3) q) →
      (q.Extension 2 ≃+* q.Extension 2) × (singularPointHom sigma H).range :=
    fun f => (tau f,⟨singularPointHom sigma H (g f),⟨g f,rfl⟩⟩)
  have hinj : Function.Injective encode := by
    intro f k he
    have ht : tau f = tau k := congrArg Prod.fst he
    have hp : singularPointHom sigma H (g f) = singularPointHom sigma H (g k) :=
      congrArg (fun z : (q.Extension 2 ≃+* q.Extension 2) × (singularPointHom sigma H).range => z.2.val) he
    have hj : Function.Injective (fun a : MulAut (CFSG.Models.TwistedA (s + 3) q) =>
        (unitaryOrthogonalityActionHom q s a).val) :=
      (unitaryHermitianSingularPointEquiv q s).permCongrHom.injective.comp
        (unitarySingularPointActionHom_injective q s)
    apply hj
    apply Equiv.ext
    intro P
    apply Subtype.ext
    rw [hpoints f,hpoints k,ht]
    have hP := congrArg (fun e : Equiv.Perm (SingularPoint sigma (H : Mat (q.Extension 2) (s + 3))) =>
      (e P).val) hp
    change P.val.map (g f).val.toLinearMap = P.val.map (g k).val.toLinearMap at hP
    rw [hP]
  letI : Finite (similitudes sigma H) := inferInstance
  letI : Finite (singularPointHom sigma H).range :=
    Finite.of_surjective (singularPointHom sigma H).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hh := Nat.card_le_card_of_injective encode hinj
  rw [Nat.card_prod,quadraticExtension_card_ringAut] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (unitary_similitude_pointImage_card_le_naturalFixed q (s + 3)))

theorem unitary_outer_card_le_of_aut_naturalFixed_bound (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA (s + 3) q))
    (hAut : Nat.card (MulAut (CFSG.Models.TwistedA (s + 3) q)) ≤
      (2 * q.exponent) * Nat.card (CFSGTwistedAUpperUnipotent.naturalFixed (s + 3) q)) :
    Nat.card (Outer (CFSG.Models.TwistedA (s + 3) q)) ≤ 2 * q.exponent * (s + 4) := by
  letI : Finite (CFSG.Models.TwistedA (s + 3) q) :=
    Finite.of_surjective (unitaryProjectiveCover q s) (unitaryProjectiveCover_surjective q s)
  apply CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound hn
  calc
    _ ≤ (2 * q.exponent) * Nat.card (CFSGTwistedAUpperUnipotent.naturalFixed (s + 3) q) := hAut
    _ ≤ (2 * q.exponent) * ((s + 4) * Nat.card (CFSG.Models.TwistedA (s + 3) q)) :=
      Nat.mul_le_mul_left _ (unitary_naturalFixed_card_le_projective_mul_dimension q s)
    _ = _ := by ac_rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
