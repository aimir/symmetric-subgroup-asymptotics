import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
# Dimension-sensitive order bounds for primitive affine profiles

The coarse affine estimate counts every automorphism of the translation
group as an arbitrary function.  For an elementary abelian translation
group this loses a full factor of the affine degree in the exponent.

This file keeps the vector-space chart produced by the primitive affine
theorem.  A group automorphism of the translation group is automatically
linear over its prime field, hence is determined by its values on a basis.
Consequently a profile of degree `p^d` has point stabilizer of order at most
`(p^d)^d` and ambient order at most `(p^d)^(d+1)`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  (P : PrimitiveAffineProfile L Ω)

local instance : Fact P.p.Prime := ⟨P.p_prime⟩

section Linearization

variable {V : Type} [AddCommGroup V] [Module (ZMod P.p) V]

/-- Conjugate an automorphism of the literal translation subgroup through
an elementary-abelian chart and regard the resulting additive map as a
`ZMod p`-linear map. -/
def linearizedAut (e : P.V ≃* Multiplicative V) :
    (P.V ≃* P.V) → (V →ₗ[ZMod P.p] V) := fun f =>
  ((AddEquiv.toMultiplicative.symm
      ((e.symm.trans f).trans e)).toAddMonoidHom).toZModLinearMap P.p

theorem linearizedAut_injective (e : P.V ≃* Multiplicative V) :
    Function.Injective (P.linearizedAut e) := by
  intro f g hfg
  have haddHom :
      (AddEquiv.toMultiplicative.symm ((e.symm.trans f).trans e)).toAddMonoidHom =
        (AddEquiv.toMultiplicative.symm ((e.symm.trans g).trans e)).toAddMonoidHom :=
    AddMonoidHom.toZModLinearMap_injective P.p hfg
  have hadd :
      AddEquiv.toMultiplicative.symm ((e.symm.trans f).trans e) =
        AddEquiv.toMultiplicative.symm ((e.symm.trans g).trans e) :=
    AddEquiv.toAddMonoidHom_injective haddHom
  have hconj : (e.symm.trans f).trans e = (e.symm.trans g).trans e :=
    AddEquiv.toMultiplicative.symm.injective hadd
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hv : e (f x) = e (g x) := by
    simpa using DFunLike.congr_fun hconj (e x)
  exact congrArg Subtype.val (e.injective hv)

/-- Linear maps on a finite-dimensional space are determined freely by
their values on a basis. -/
theorem card_linearMap_eq_pow_finrank [Finite V]
    [FiniteDimensional (ZMod P.p) V] :
    Nat.card (V →ₗ[ZMod P.p] V) =
      Nat.card V ^ Module.finrank (ZMod P.p) V := by
  let b := Module.finBasis (ZMod P.p) V
  calc
    Nat.card (V →ₗ[ZMod P.p] V) =
        Nat.card (Fin (Module.finrank (ZMod P.p) V) → V) :=
      Nat.card_congr (b.constr (ZMod P.p)).symm.toEquiv
    _ = Nat.card V ^ Nat.card (Fin (Module.finrank (ZMod P.p) V)) :=
      Nat.card_fun
    _ = Nat.card V ^ Module.finrank (ZMod P.p) V := by simp

/-- The automorphism group of a finite elementary abelian group has at most
`|V|^d` elements, where `d` is its prime-field dimension. -/
theorem mulEquiv_card_le_pow_finrank [Finite V]
    [FiniteDimensional (ZMod P.p) V]
    (e : P.V ≃* Multiplicative V) :
    Nat.card (P.V ≃* P.V) ≤
      Nat.card V ^ Module.finrank (ZMod P.p) V := by
  let b := Module.finBasis (ZMod P.p) V
  letI : Finite (V →ₗ[ZMod P.p] V) :=
    Finite.of_injective (fun f => (b.constr (ZMod P.p)).symm f)
      (b.constr (ZMod P.p)).symm.injective
  calc
    Nat.card (P.V ≃* P.V) ≤ Nat.card (V →ₗ[ZMod P.p] V) :=
      Nat.card_le_card_of_injective (P.linearizedAut e)
        (P.linearizedAut_injective e)
    _ = _ := P.card_linearMap_eq_pow_finrank

end Linearization

/-- A vector-space chart identifies the affine degree with the corresponding
prime power, with the actual vector-space dimension as exponent. -/
theorem degree_eq_prime_pow_finrank [Finite L] [Finite Ω]
    {V : Type} [AddCommGroup V] [Module (ZMod P.p) V]
    [FiniteDimensional (ZMod P.p) V] [Finite V]
    (e : P.V ≃* Multiplicative V) (x : Ω) :
    Nat.card Ω = P.p ^ Module.finrank (ZMod P.p) V := by
  calc
    Nat.card Ω = Nat.card P.V := (P.card_eq x).symm
    _ = Nat.card V := Nat.card_congr e.toEquiv
    _ = P.p ^ Module.finrank (ZMod P.p) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := V),
        Nat.card_zmod]

/-- The faithful complement of a primitive affine profile is bounded by the
dimension-sensitive linear-map count. -/
theorem complement_card_le_degree_pow_finrank
    [Finite L] [Finite Ω] [FaithfulSMul L Ω]
    {V : Type} [AddCommGroup V] [Module (ZMod P.p) V]
    [FiniteDimensional (ZMod P.p) V] [Finite V]
    (e : P.V ≃* Multiplicative V) (x : Ω) :
    Nat.card (P.complement x) ≤
      Nat.card Ω ^ Module.finrank (ZMod P.p) V := by
  calc
    Nat.card (P.complement x) ≤ Nat.card (P.V ≃* P.V) :=
      P.complement_card_le_mulEquiv x
    _ ≤ Nat.card V ^ Module.finrank (ZMod P.p) V :=
      P.mulEquiv_card_le_pow_finrank e
    _ = Nat.card Ω ^ Module.finrank (ZMod P.p) V := by
      have hcard : Nat.card V = Nat.card Ω :=
        (Nat.card_congr e.toEquiv).symm.trans (P.card_eq x)
      rw [hcard]

/-- The whole affine group has order at most `w^(d+1)` for degree `w` and
translation dimension `d`. -/
theorem card_le_degree_pow_finrank_succ
    [Finite L] [Finite Ω] [FaithfulSMul L Ω]
    {V : Type} [AddCommGroup V] [Module (ZMod P.p) V]
    [FiniteDimensional (ZMod P.p) V] [Finite V]
    (e : P.V ≃* Multiplicative V) (x : Ω) :
    Nat.card L ≤
      Nat.card Ω ^ (Module.finrank (ZMod P.p) V + 1) := by
  have hfactor := (P.isComplement'_complement x).card_mul
  calc
    Nat.card L = Nat.card P.V * Nat.card (P.complement x) := hfactor.symm
    _ ≤ Nat.card Ω *
        Nat.card Ω ^ Module.finrank (ZMod P.p) V := by
      rw [P.card_eq x]
      exact Nat.mul_le_mul_left _ (P.complement_card_le_degree_pow_finrank e x)
    _ = Nat.card Ω ^ (Module.finrank (ZMod P.p) V + 1) := by
      rw [pow_succ]
      exact Nat.mul_comm _ _

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
