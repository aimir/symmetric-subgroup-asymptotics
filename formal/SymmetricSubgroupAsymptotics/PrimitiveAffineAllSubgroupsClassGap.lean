import SymmetricSubgroupAsymptotics.AffineClassOnePowerGapNumerics
import SymmetricSubgroupAsymptotics.BinaryThirtyTwoElementSemidirectClassGap
import SymmetricSubgroupAsymptotics.AffineDegreeEightSubgroupClassGap
import SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassGap
import SymmetricSubgroupAsymptotics.AffineDegreeSixteenSubgroupClassGap
import SymmetricSubgroupAsymptotics.AffineClassFiveDegreeResidual

/-! Every subgroup of the same original faithful primitive affine action
of degree at least five has the one-power GM gap. Prime powers below64
are arithmetic cases only; the prime, square, cube and large-degree
families are uniform, and the binary linear charts cover8,16,32. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineAllSubgroupsClassGap

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_gap_thirtyTwo
    (hprimitive : MulAction.IsPreprimitive G X) (x : X)
    (hdegree : Nat.card X = 32) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  have hp : P.p = 2 := PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow
    P x 5 (by simpa using hdegree)
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  letI : CommGroup P.V := inferInstance
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  let a : Additive P.V ≃+ C.V := C.equiv.toAdditive
  letI : Module (ZMod P.p) (Additive P.V) := a.module (ZMod P.p)
  let e := P.semidirectEquiv x
  let L := H.map e.symm.toMonoidHom
  letI : Finite L := Finite.of_injective (fun z : L => z.val) Subtype.val_injective
  letI : Finite (ConjClasses L) :=
    Finite.of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective
  let b := e.symm.subgroupMap H
  have hc : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses L) :=
    Nat.card_le_card_of_surjective (ConjClasses.map b.symm.toMonoidHom)
      (ConjClasses.map_surjective b.symm.surjective)
  have hV : Nat.card P.V = 32 := (P.card_eq x).trans hdegree
  have hL := BinaryThirtyTwoElementSemidirectClassGap.subgroup_class_cube_gap
    hp hV (P.complementAction x) (P.complementAction_injective x) L
  exact (Nat.pow_le_pow_left hc 3).trans (by simpa only [P.card_eq x] using hL)

include P in
private theorem square_gap (x : X) (hp : 5 ≤ P.p)
    (hdegree : Nat.card X = P.p ^ 2) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hs : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  have ho := AffinePrimePowerOrderBound.card_le_degree_mul_prime_log_power P x
  rw [hdegree, Nat.log_pow P.p_prime.one_lt] at ho
  have hbound : Nat.card (ConjClasses H) ≤ P.p ^ 6 := by
    calc
      Nat.card (ConjClasses H) ≤ P.p ^ 2 * (P.p ^ 2) ^ 2 := (hc.trans hs).trans ho
      _ = P.p ^ 6 := by ring
  rw [hdegree]
  have h := Nat.pow_le_pow_left hbound 3
  rw [← pow_mul] at h
  exact h.trans (AffineClassOnePowerGapNumerics.square_degree_gap P.p hp)

include P in
private theorem cube_gap (x : X) (hp : 3 ≤ P.p)
    (hdegree : Nat.card X = P.p ^ 3) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hs : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  have ho := AffinePrimePowerOrderBound.card_le_degree_mul_prime_log_power P x
  rw [hdegree, Nat.log_pow P.p_prime.one_lt] at ho
  have hbound : Nat.card (ConjClasses H) ≤ P.p ^ 12 := by
    calc
      Nat.card (ConjClasses H) ≤ P.p ^ 3 * (P.p ^ 3) ^ 3 := (hc.trans hs).trans ho
      _ = P.p ^ 12 := by ring
  rw [hdegree]
  have h := Nat.pow_le_pow_left hbound 3
  rw [← pow_mul] at h
  exact h.trans (AffineClassOnePowerGapNumerics.cube_degree_gap P.p hp)

include P in
theorem subgroup_class_cube_gap (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hn : 5 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  by_cases hlarge : 64 ≤ Nat.card X
  · have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    have hs : Nat.card H ≤ Nat.card G :=
      Nat.card_le_card_of_injective H.subtype Subtype.val_injective
    exact (Nat.pow_le_pow_left ((hc.trans hs).trans (P.card_le_domain_pow_log x)) 3).trans
      (AffineClassOnePowerGapNumerics.domain_pow_log_cube_gap (Nat.card X) hlarge)
  by_cases hprime : Nat.Prime (Nat.card X)
  · exact (Nat.pow_le_pow_left
      (PrimeDegreeAffineAllSubgroupsClassBound.subgroup_class_card_le_degree P x hprime H) 3).trans
      (AffineClassOnePowerGapNumerics.degree_cube_gap (Nat.card X) hn)
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  obtain ⟨d, hd⟩ := P.V_pgroup.exists_card_eq
  have heq : Nat.card X = P.p ^ d := (P.card_eq x).symm.trans hd
  have hres := SmallAffinePrimePowerDegrees.residual_of_small_prime_power
    P.p d (Nat.card X) P.p_prime heq (by omega) (by omega) (fun h => hprime h.2)
  have hdvd : P.p ∣ Nat.card X := by
    have hh := P.V_pgroup.card_eq_or_dvd
    rw [P.card_eq x] at hh
    exact hh.resolve_left (by omega)
  rcases hres with h4 | h5 | h7 | h8 | h9 | h16 | h25 | h27 | h32 | h49
  · omega
  · exact False.elim (hprime (by rw [h5]; decide))
  · exact False.elim (hprime (by rw [h7]; decide))
  · exact AffineDegreeEightSubgroupClassGap.subgroup_class_cube_gap P hprimitive x h8 H
  · exact AffineDegreeNineSubgroupClassGap.subgroup_class_cube_gap P x h9 H
  · exact AffineDegreeSixteenSubgroupClassGap.subgroup_class_cube_gap P hprimitive x h16 H
  · have hbase : P.p = 5 := Nat.prime_eq_prime_of_dvd_pow (m := 2) P.p_prime
      (by decide : Nat.Prime 5) (by simpa only [h25, show (5 : ℕ) ^ 2 = 25 by decide] using hdvd)
    exact square_gap P x (by rw [hbase])
      (by simpa only [hbase, show (5 : ℕ) ^ 2 = 25 by decide] using h25) H
  · have hbase : P.p = 3 := Nat.prime_eq_prime_of_dvd_pow (m := 3) P.p_prime
      (by decide : Nat.Prime 3) (by simpa only [h27, show (3 : ℕ) ^ 3 = 27 by decide] using hdvd)
    exact cube_gap P x (by rw [hbase])
      (by simpa only [hbase, show (3 : ℕ) ^ 3 = 27 by decide] using h27) H
  · exact subgroup_class_cube_gap_thirtyTwo P hprimitive x h32 H
  · have hbase : P.p = 7 := Nat.prime_eq_prime_of_dvd_pow (m := 2) P.p_prime
      (by decide : Nat.Prime 7) (by simpa only [h49, show (7 : ℕ) ^ 2 = 49 by decide] using hdvd)
    exact square_gap P x (by rw [hbase]; decide)
      (by simpa only [hbase, show (7 : ℕ) ^ 2 = 49 by decide] using h49) H

end SymmetricSubgroupAsymptotics.PrimitiveAffineAllSubgroupsClassGap
