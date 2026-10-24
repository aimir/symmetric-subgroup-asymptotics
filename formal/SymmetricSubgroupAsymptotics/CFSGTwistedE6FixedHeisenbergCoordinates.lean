import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedBilinearPairing
import Mathlib.LinearAlgebra.Dual.Basis

/-! Standard Heisenberg coordinates inside the actual signed fixed E6
arrays. A basis and its actual pairing-dual retain the literal central
delta; no coordinate-sign normalization or fixed-quotient lifting is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedHeisenbergCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGHeisenbergCoordinateGroup CFSGCommutingParameterTwist
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGTwistedE6HeisenbergTwistCompatibility CFSGTwistedE6SignedArrayCoordinates
open CFSGTwistedE6FixedBilinearPairing
open Module

def firstBasis (q : CFSG.PrimePower) : Basis (Fin 10) (fixedField q) (First q) :=
  Module.finBasisOfFinrankEq (fixedField q) (First q) (first_finrank q)

def firstCoordinates (q : CFSG.PrimePower) : First q ≃ₗ[fixedField q] (Fin 10 → fixedField q) :=
  (firstBasis q).equivFun

def secondCoordinates (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Second q ≃ₗ[fixedField q] (Fin 10 → fixedField q) :=
  (scalarPairingEquiv q delta hdelta).trans (firstBasis q).dualBasis.equivFun

theorem pairing_eq_coordinate_sum (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) (b : Second q) (a : First q) :
    scalarPairing q delta hdelta b a =
      ∑ i : Fin 10, firstCoordinates q a i * secondCoordinates q delta hdelta b i := by
  have hh := congrArg (fun z : First q => scalarPairing q delta hdelta b z)
    ((firstBasis q).sum_repr a)
  simpa only [map_sum, map_smul, smul_eq_mul, firstCoordinates, secondCoordinates,
    LinearEquiv.trans_apply, LinearMap.linearEquivOfInjective_apply,
    Basis.equivFun_apply, Basis.dualBasis_repr] using hh.symm

theorem dot_coordinates (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) (b a : Fin 10 → fixedField q) :
    dot ((secondCoordinates q delta hdelta).symm b).val ((firstCoordinates q).symm a).val =
      delta.val * ((dot b a : fixedField q) : q.Extension 2) := by
  have hh := scalarPairing_scaled q delta hdelta
    ((secondCoordinates q delta hdelta).symm b) ((firstCoordinates q).symm a)
  rw [pairing_eq_coordinate_sum, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at hh
  have hc : (∑ i : Fin 10, a i * b i) = dot b a := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hc] at hh
  exact hh.symm

def coordinateHom (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Element (fixedField q) 10 →* Element (q.Extension 2) 10 where
  toFun g := ⟨((firstCoordinates q).symm g.a).val,
    ((secondCoordinates q delta hdelta).symm g.b).val, delta.val * (g.c : q.Extension 2)⟩
  map_one' := by
    apply Element.ext
    · change ((firstCoordinates q).symm 0).val = 0
      rw [map_zero]
      rfl
    · change ((secondCoordinates q delta hdelta).symm 0).val = 0
      rw [map_zero]
      rfl
    · change delta.val * (0 : q.Extension 2) = 0
      exact mul_zero _
  map_mul' g h := by
    apply Element.ext
    · change ((firstCoordinates q).symm (g.a + h.a)).val =
        ((firstCoordinates q).symm g.a).val + ((firstCoordinates q).symm h.a).val
      exact congrArg (fun a : First q => a.val) ((firstCoordinates q).symm.map_add g.a h.a)
    · change ((secondCoordinates q delta hdelta).symm (g.b + h.b)).val =
        ((secondCoordinates q delta hdelta).symm g.b).val +
          ((secondCoordinates q delta hdelta).symm h.b).val
      exact congrArg (fun b : Second q => b.val)
        ((secondCoordinates q delta hdelta).symm.map_add g.b h.b)
    · change delta.val * ((g.c + h.c + dot g.b h.a : fixedField q) : q.Extension 2) =
        delta.val * (g.c : q.Extension 2) + delta.val * (h.c : q.Extension 2) +
          dot ((secondCoordinates q delta hdelta).symm g.b).val
            ((firstCoordinates q).symm h.a).val
      rw [dot_coordinates]
      change delta.val * ((g.c : q.Extension 2) + (h.c : q.Extension 2) +
        ((dot g.b h.a : fixedField q) : q.Extension 2)) = _
      ring

theorem coordinateHom_injective (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) : Function.Injective (coordinateHom q delta hdelta) := by
  intro g h he
  have hga : (firstCoordinates q).symm g.a = (firstCoordinates q).symm h.a :=
    Subtype.ext (congrArg (fun z : Element (q.Extension 2) 10 => z.a) he)
  have hgb : (secondCoordinates q delta hdelta).symm g.b =
      (secondCoordinates q delta hdelta).symm h.b :=
    Subtype.ext (congrArg (fun z : Element (q.Extension 2) 10 => z.b) he)
  have hgc : delta.val * (g.c : q.Extension 2) = delta.val * (h.c : q.Extension 2) :=
    congrArg (fun z : Element (q.Extension 2) 10 => z.c) he
  exact Element.ext ((firstCoordinates q).symm.injective hga)
    ((secondCoordinates q delta hdelta).symm.injective hgb)
    (Subtype.ext (mul_left_cancel₀ hdelta hgc))

private theorem central_scaled_fixed (q : CFSG.PrimePower) (delta : Central q)
    (c : fixedField q) :
    (centralWeight : q.Extension 2) *
      definingFieldAutomorphism q 2 (delta.val * (c : q.Extension 2)) =
        delta.val * (c : q.Extension 2) := by
  have hd : definingFieldAutomorphism q 2 delta.val =
      (centralWeight : q.Extension 2) * delta.val := delta.property
  have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) := c.property
  have hs : (centralWeight : q.Extension 2) * (centralWeight : q.Extension 2) = 1 := by
    rcases centralWeight_unit with h | h <;> simp only [h, Int.cast_one, Int.cast_neg] <;> ring
  rw [map_mul, hd, hc, ← mul_assoc, ← mul_assoc, hs, one_mul]

theorem coordinateHom_fixed (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) (g : Element (fixedField q) 10) :
    coordinateTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (coordinateHom q delta hdelta g) = coordinateHom q delta hdelta g := by
  apply Element.ext
  · exact (mem_arraySpace_iff q firstWeight _).mp ((firstCoordinates q).symm g.a).property
  · exact (mem_arraySpace_iff q secondWeight _).mp
      ((secondCoordinates q delta hdelta).symm g.b).property
  · exact central_scaled_fixed q delta g.c

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedHeisenbergCoordinates
