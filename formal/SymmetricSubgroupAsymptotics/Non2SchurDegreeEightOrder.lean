import SymmetricSubgroupAsymptotics.Non2SchurFaithfulDegree
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The faithful product-degree-eight order

At Schur product degree eight, parity excludes Schur rank one.  The row is
therefore two-dimensional over its four-element Schur field, and a faithful
original group embeds in `GL₂(4)`, of order `180`.  This is the exact order
input needed by the one-fifth fixed-space branch.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {B X A : Type} [Group B] [Finite B] [Finite X] [MulAction B X]
    [MulAction.IsPretransitive B X]
    [AddCommGroup A] [Module (ZMod 2) A]
    [FiniteDimensional (ZMod 2) A]

/-- A faithful product-degree-eight simple Schur row forces the original
group order to divide `|GL₂(4)|=180`. -/
theorem group_natCard_dvd_180_of_faithful_schurProductDegree_eight
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hfaithful : schurSimpleActionKernel sigma S = ⊥)
    (heven : Even (Nat.card X))
    (height : schurSimpleProductDegree sigma S = 8) :
    Nat.card B ∣ 180 := by
  classical
  let E := Module.End (ZMod 2)[B] S
  let f := Module.finrank (ZMod 2) E
  let d := Module.finrank E S
  letI : FiniteDimensional (ZMod 2) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[B] S
  letI : Finite S := Module.finite_of_finite (ZMod 2)
  have htower : Module.finrank (ZMod 2) S = f * d := by
    simpa [E, f, d] using
      (schur_simple_finrank_tower
        (k := ZMod 2) (R := (ZMod 2)[B]) (X := S))
  have hSpos : 0 < Module.finrank (ZMod 2) S := Module.finrank_pos
  have hfdpos : 0 < f * d := by omega
  have hfpos : 0 < f := pos_of_mul_pos_left hfdpos (Nat.zero_le d)
  have hdpos : 0 < d := pos_of_mul_pos_right hfdpos (Nat.zero_le f)
  letI : FiniteDimensional (ZMod 2) E :=
    FiniteDimensional.of_finrank_pos hfpos
  letI : Finite E := Module.finite_of_finite (ZMod 2)
  letI : Field E := littleWedderburn E
  letI : FiniteDimensional E S :=
    FiniteDimensional.of_finrank_pos hdpos
  have hproduct : f * d * d = 8 := by
    have h : schurSimpleProductDegree sigma S = f * d * d := by
      simp only [schurSimpleProductDegree, htower]
      rfl
    omega
  have hEcard : Nat.card E = 2 ^ f := by
    have hcard : Nat.card E = Nat.card (ZMod 2) ^
        Module.finrank (ZMod 2) E := Module.natCard_eq_pow_finrank
    simpa [f, Nat.card_zmod] using hcard
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation sigma S)
  have hker : rhoE.ker = ⊥ := by
    rw [MonoidHom.ker_toHomUnits,
      schurSimpleActionEndRepresentation_ker, hfaithful]
  have hrhoInjective : Function.Injective rhoE :=
    (MonoidHom.ker_eq_bot_iff rhoE).mp hker
  have hdne : d ≠ 1 := by
    intro hd1
    have hd1' : Module.finrank E S = 1 := by simpa [d] using hd1
    have hEndFinrank : Module.finrank E (Module.End E S) = 1 := by
      rw [Module.finrank_linearMap, hd1']
    let eEnd : E ≃+* Module.End E S :=
      RingEquiv.ofBijective (algebraMap E (Module.End E S))
        (Module.Free.bijective_algebraMap_of_finrank_eq_one
          (R := E) (S := Module.End E S) hEndFinrank)
    have hUnits : Nat.card (Module.End E S)ˣ = 2 ^ f - 1 := by
      rw [← Nat.card_congr (Units.mapEquiv eEnd.toMulEquiv).toEquiv,
        Nat.card_units, hEcard]
    have hBdvd : Nat.card B ∣ 2 ^ f - 1 := by
      rw [← hUnits]
      exact Subgroup.card_dvd_of_injective rhoE hrhoInjective
    have hfne : f ≠ 0 := by omega
    have hoddPow : Even (2 ^ f) := even_two.pow_of_ne_zero hfne
    have hpowpos : 0 < 2 ^ f := pow_pos (by norm_num : 0 < (2 : ℕ)) f
    have hodd : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd (by omega) hoddPow odd_one
    have hBodd : Odd (Nat.card B) := hodd.of_dvd_nat hBdvd
    have hXdB := transitive_natCard_dvd_group_natCard (B := B) x
    have hXodd : Odd (Nat.card X) := hBodd.of_dvd_nat hXdB
    exact Nat.not_even_iff_odd.mpr hXodd heven
  have hdle : d ≤ 2 := by nlinarith
  have hd2 : d = 2 := by omega
  have hf2 : f = 2 := by
    rw [hd2] at hproduct
    omega
  have hEfour : Nat.card E = 4 := by rw [hEcard, hf2]; decide
  have hd2' : Module.finrank E S = 2 := by simpa [d] using hd2
  let basis : Module.Basis (Fin 2) E S :=
    Module.finBasisOfFinrankEq E S hd2'
  have hGL : Nat.card (Module.End E S)ˣ = 180 := by
    rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' basis).toEquiv,
      Matrix.card_GL_field]
    simp only [Fintype.card_eq_nat_card]
    rw [hEfour]
    decide
  rw [← hGL]
  exact Subgroup.card_dvd_of_injective rhoE hrhoInjective

end SymmetricSubgroupAsymptotics

end
