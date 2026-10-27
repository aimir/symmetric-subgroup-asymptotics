import SymmetricSubgroupAsymptotics.MersennePrimePowerRigidity
import SymmetricSubgroupAsymptotics.External.CFSG.Parameters
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverBinomialOrbits
import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelSolvable

/-! Arithmetic consumed on the SAME retained PSL2 field and correlated
index-three cover. A binary field-successor hypothesis is still genuine
input to this local theorem; arbitrary-action classification and binary
lifts are NOT concluded from this arithmetic. Primality/coprimality of
the field order are proved internally, rather than imported callbacks.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoMersenneParameters
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates
open CFSGPSLTwoProductTorusCover CFSGPSLTwoCorrelatedCoverProjection

theorem parameters (q : CFSG.PrimePower) (a : ℕ)
    (hq : 4≤q.order) (hsize : q.order+1=2^a) :
    3≤a ∧ q.exponent=1 ∧ q.prime=2^a-1 ∧ Nat.Prime (2^a-1) := by
  have ha : 3≤a := by
    by_contra hh
    have hp : 2^a≤2^2 := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega)
    norm_num at hp
    omega
  have hplus : 2∣q.order+1 := by
    rw [hsize]
    exact dvd_pow_self 2 (by omega : a≠0)
  have hne : q.prime≠2 := by
    intro heq
    have hdiv : 2∣q.order := by
      rw [CFSG.PrimePower.order,heq]
      exact dvd_pow_self 2 q.exponent_pos.ne'
    have hh := Nat.dvd_sub hplus hdiv
    norm_num at hh
  have hsum : q.prime^q.exponent+1=2^a := by
    simpa only [CFSG.PrimePower.order] using hsize
  have hex := MersennePrimePowerRigidity.exponent_eq_one_of_odd_pow_add_one_eq_two_pow
    q.prime q.exponent a q.prime_isPrime.two_le (q.prime_isPrime.odd_of_ne_two hne)
    (by have hh := q.exponent_pos; omega) (by omega) hsum
  have hp : q.prime=2^a-1 := by
    rw [hex,pow_one] at hsum
    omega
  refine ⟨ha,hex,hp,?_⟩
  rw [←hp]
  exact q.prime_isPrime

theorem order_prime (q : CFSG.PrimePower) (a : ℕ)
    (hq : 4≤q.order) (hsize : q.order+1=2^a) : Nat.Prime q.order := by
  obtain ⟨_,hex,_,_⟩ := parameters q a hq hsize
  rw [CFSG.PrimePower.order,hex,pow_one]
  exact q.prime_isPrime

theorem field_card_coprime_three (q : CFSG.PrimePower) (a : ℕ)
    (hq : 4≤q.order) (hsize : q.order+1=2^a) : (Nat.card q.Field).Coprime 3 := by
  rw [CFSG.PrimePower.card_field]
  apply (order_prime q a hq hsize).coprime_iff_not_dvd.mpr
  intro hd
  have hh := Nat.le_of_dvd (by decide : 0<3) hd
  omega

/-- Literal binomial labels and orbit sizes now have exactly the Mersenne
prime and a>=3 arithmetic needed by the raw exceptional formula. The same
normal H is retained throughout; there is no product-fibre replacement. -/
theorem correlated_binomial_orbits (q : CFSG.PrimePower) (a : ℕ)
    (hq : 4≤q.order) (hsize : q.order+1=2^a)
    {J : Type} [Fintype J] [DecidableEq J]
    (H : Subgroup (J → projectiveBorel (F := q.Field))) [H.Normal]
    (hindex : H.index=3) :
    3≤a ∧ Nat.Prime (2^a-1) ∧ IsSolvable (J → projectiveBorel (F := q.Field)) ∧
    ∃ index : MulAction.orbitRel.Quotient
        (J → projectiveBorel (F := q.Field)) (Cover H) ≃
        (Σ k : Fin (Fintype.card J+1),Fin ((Fintype.card J).choose k.val)),
      Nat.card (MulAction.orbitRel.Quotient
        (J → projectiveBorel (F := q.Field)) (Cover H))=2^Fintype.card J ∧
      ∀ o : MulAction.orbitRel.Quotient
        (J → projectiveBorel (F := q.Field)) (Cover H),
        Nat.card o.orbit=3*(2^a-1)^((index o).1.val) := by
  have hp := parameters q a hq hsize
  have hcop := field_card_coprime_three q a hq hsize
  let index := CFSGPSLTwoCorrelatedCoverBinomialOrbits.index
    (F := q.Field) H hindex hcop
  refine ⟨hp.1,hp.2.2.2,
    CFSGPSLTwoProductBorelSolvable.borelPower_isSolvable (F := q.Field) (J := J),
    index,CFSGPSLTwoCorrelatedCoverBinomialOrbits.orbit_count H hindex hcop,?_⟩
  intro o
  have horder : q.order=2^a-1 := by omega
  have hh := CFSGPSLTwoCorrelatedCoverBinomialOrbits.orbit_card H hindex hcop o
  simpa only [CFSG.PrimePower.card_field,horder] using hh

end SymmetricSubgroupAsymptotics.CFSGPSLTwoMersenneParameters
