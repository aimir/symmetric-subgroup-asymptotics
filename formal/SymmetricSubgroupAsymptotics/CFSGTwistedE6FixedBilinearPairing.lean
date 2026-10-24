import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedArrayNondegeneracy
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.BilinearMap

/-! The literal descended X/Y arrays are dual ten-dimensional vector
spaces.  The central coordinate is measured in a retained nonzero signed
central vector delta.  Its nondegeneracy comes from actual trace test
vectors, with no fixed-quotient lifting or form-recognition input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedBilinearPairing
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGHeisenbergCoordinateGroup CFSGCommutingParameterTwist
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGTwistedE6HeisenbergTwistCompatibility CFSGTwistedE6HeisenbergFixedPairing
open CFSGTwistedE6SignedArrayCoordinates CFSGQuadraticSignedFixedCoordinates
open CFSGTwistedE6FixedArrayNondegeneracy

abbrev First (q : CFSG.PrimePower) := arraySpace q firstWeight
abbrev Second (q : CFSG.PrimePower) := arraySpace q secondWeight
abbrev Central (q : CFSG.PrimePower) := signedLine q centralWeight

private theorem array_finrank (q : CFSG.PrimePower) (w : Fin 10 → ℤ)
    (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hc : ∀ i, (w (partner i) : q.Extension 2) * (w i : q.Extension 2) = 1) :
    Module.finrank (fixedField q) (arraySpace q w) = 10 := by
  apply Nat.pow_right_injective (CFSGTwistedAQuadraticTrace.order_two_le q)
  have h := Module.natCard_eq_pow_finrank (K := fixedField q) (V := arraySpace q w)
  rw [fixedField_card, arraySpace_card q w hw hc] at h
  exact h.symm

theorem first_finrank (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (First q) = 10 :=
  array_finrank q firstWeight firstWeight_unit (firstWeight_partner_mul (q.Extension 2))

theorem second_finrank (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (Second q) = 10 :=
  array_finrank q secondWeight secondWeight_unit (secondWeight_partner_mul (q.Extension 2))

def signedDot (q : CFSG.PrimePower) :
    Second q →ₗ[fixedField q] First q →ₗ[fixedField q] Central q where
  toFun b :=
    { toFun := fun a => ⟨dot b.val a.val, dot_signed_fixed q b.val a.val
        ((mem_arraySpace_iff q secondWeight _).mp b.property)
        ((mem_arraySpace_iff q firstWeight _).mp a.property)⟩
      map_add' := fun a a' => by
        apply Subtype.ext
        change dot b.val (a.val + a'.val) = dot b.val a.val + dot b.val a'.val
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        apply Subtype.ext
        change (∑ i, b.val i * ((c : q.Extension 2) * a.val i)) =
          (c : q.Extension 2) * (∑ i, b.val i * a.val i)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' b b' := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change dot (b.val + b'.val) a.val = dot b.val a.val + dot b'.val a.val
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c b := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change (∑ i, ((c : q.Extension 2) * b.val i) * a.val i) =
      (c : q.Extension 2) * (∑ i, b.val i * a.val i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem signedDot_apply (q : CFSG.PrimePower) (b : Second q) (a : First q) :
    (signedDot q b a).val = dot b.val a.val := rfl

def centralCoordinates (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Central q ≃ₗ[fixedField q] fixedField q :=
  (lineEquiv q centralWeight centralWeight_unit delta hdelta).symm

def scalarPairing (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Second q →ₗ[fixedField q] Module.Dual (fixedField q) (First q) :=
  (signedDot q).compr₂ (centralCoordinates q delta hdelta).toLinearMap

theorem scalarPairing_scaled (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) (b : Second q) (a : First q) :
    delta.val * (scalarPairing q delta hdelta b a : q.Extension 2) = dot b.val a.val := by
  have hh := congrArg (fun z : Central q => z.val)
    ((lineEquiv q centralWeight centralWeight_unit delta hdelta).apply_symm_apply
      (signedDot q b a))
  change (scalarPairing q delta hdelta b a : q.Extension 2) * delta.val = dot b.val a.val at hh
  exact (mul_comm _ _).trans hh

theorem scalarPairing_injective (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) : Function.Injective (scalarPairing q delta hdelta) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  by_contra hne
  have hbval : b.val ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨a, ha⟩ := exists_first_pairing q b hbval delta
  have hz : scalarPairing q delta hdelta b a = 0 :=
    congrArg (fun f : Module.Dual (fixedField q) (First q) => f a) hb
  have hh := scalarPairing_scaled q delta hdelta b a
  rw [hz, ZeroMemClass.coe_zero, mul_zero, ha] at hh
  exact hdelta hh.symm

def scalarPairingEquiv (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Second q ≃ₗ[fixedField q] Module.Dual (fixedField q) (First q) :=
  LinearMap.linearEquivOfInjective (scalarPairing q delta hdelta)
    (scalarPairing_injective q delta hdelta) (by
      rw [Subspace.dual_finrank_eq, first_finrank, second_finrank])

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedBilinearPairing
