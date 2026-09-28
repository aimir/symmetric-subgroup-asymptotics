import SymmetricSubgroupAsymptotics.Non2SchurScalarOrbit

/-!
# The first faithful Schur product degrees

If the selected simple row is faithful, its original group embeds in the
units of the endomorphism ring over the finite Schur field.  A transitive
even action rules out Schur rank one because that unit group has odd order.
Below product degree nine, the only remaining numerical profiles have Schur
rank two and product degree four or eight.  Degree four embeds the original
group in a set of cardinality sixteen, contradicting an original transitive
degree at least 24.  Hence the sole small faithful product degree is eight.
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

omit [Finite B] [Finite X] in
/-- The cardinality of a transitive finite action divides the cardinality of
its acting group. -/
theorem transitive_natCard_dvd_group_natCard (x : X) :
    Nat.card X ∣ Nat.card B := by
  rw [← MulAction.index_stabilizer_of_transitive B x]
  exact (MulAction.stabilizer B x).index_dvd_card

omit [Finite X] in
theorem transitive_natCard_le_group_natCard (x : X) :
    Nat.card X ≤ Nat.card B :=
  Nat.le_of_dvd Nat.card_pos (transitive_natCard_dvd_group_natCard x)

omit [Finite X] in
/-- A faithful binary simple row has Schur product degree eight or
at least nine in every even transitive original degree at least 24. -/
theorem schurSimpleProductDegree_eq_eight_or_nine_le_of_faithful
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hfaithful : schurSimpleActionKernel sigma S = ⊥)
    (heven : Even (Nat.card X))
    (hs : 24 ≤ Nat.card X) :
    schurSimpleProductDegree sigma S = 8 ∨
      9 ≤ schurSimpleProductDegree sigma S := by
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
  have hproduct : schurSimpleProductDegree sigma S = f * d * d := by
    simp only [schurSimpleProductDegree, htower]
    rfl
  by_cases hnine : 9 ≤ schurSimpleProductDegree sigma S
  · exact Or.inr hnine
  have hlt : f * d * d < 9 := by omega
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
  by_cases hd1 : d = 1
  · have hd1' : Module.finrank E S = 1 := by simpa [d] using hd1
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
    exact (Nat.not_even_iff_odd.mpr hXodd heven).elim
  · have hdle : d ≤ 2 := by nlinarith
    have hd2 : d = 2 := by omega
    have hfle : f ≤ 2 := by nlinarith
    by_cases hf2 : f = 2
    · left
      rw [hproduct, hd2, hf2]
    · have hf1 : f = 1 := by omega
      have hd2' : Module.finrank E S = 2 := by simpa [d] using hd2
      have hEndFinrank : Module.finrank E (Module.End E S) = 4 := by
        rw [Module.finrank_linearMap, hd2']
      letI : Finite (Module.End E S) :=
        Finite.of_injective (fun u : Module.End E S => (u : S → S))
          LinearMap.coe_injective
      have hEndCard : Nat.card (Module.End E S) = 16 := by
        have hcard : Nat.card (Module.End E S) = Nat.card E ^
            Module.finrank E (Module.End E S) :=
          Module.natCard_eq_pow_finrank (K := E) (V := Module.End E S)
        rw [hcard, hEndFinrank, hEcard, hf1]
        norm_num
      have hBunits : Nat.card B ≤ Nat.card (Module.End E S)ˣ :=
        Nat.card_le_card_of_injective rhoE hrhoInjective
      have hunitsEnd : Nat.card (Module.End E S)ˣ ≤
          Nat.card (Module.End E S) :=
        Nat.card_le_card_of_injective Units.val Units.val_injective
      have hXB := transitive_natCard_le_group_natCard (B := B) x
      omega

end SymmetricSubgroupAsymptotics

end
