import SymmetricSubgroupAsymptotics.CFSGPSLTwoMersenneParameters

/-! Arithmetic extracted from the retained exceptional degree formula.
The binary-successor relation is DERIVED from3*n^e*2^t=3*2^m, not assumed.
No arbitrary-action classification, subgroup existence or binary lift is
proved or postulated by this scalar lemma.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyExceptionalMersenneDegreeArithmetic
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates
open CFSGPSLTwoProductTorusCover CFSGPSLTwoCorrelatedCoverProjection

theorem binary_factor_of_degree_formula (n e t m : ℕ) (he : 1≤e)
    (hdegree : 3*n^e*2^t=3*2^m) :
    ∃ a : ℕ,n=2^a ∧ m=e*a+t := by
  have hc : n^e*2^t=2^m := Nat.eq_of_mul_eq_mul_left (by decide : 0<3)
    (by simpa only [mul_assoc] using hdegree)
  have hd : n∣2^m := (dvd_pow_self n (by omega : e≠0)).trans ⟨2^t,hc.symm⟩
  obtain ⟨a,_ha,hbinary⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hp : (2^a)^e*2^t=2^m := by simpa only [←hbinary] using hc
  rw [←pow_mul,←pow_add] at hp
  have hm := Nat.pow_right_injective (by decide : 2≤(2 : ℕ)) hp
  exact ⟨a,hbinary,by simpa only [Nat.mul_comm] using hm.symm⟩

/-- Exact e,a,t arithmetic and prime field order from the actual specified
prime power. No Mersenne/prime-order assumption is passed to the consumer. -/
theorem mersenne_parameters_of_degree_formula (q : CFSG.PrimePower) (e t m : ℕ)
    (hq : 4≤q.order) (he : 1≤e)
    (hdegree : 3*(q.order+1)^e*2^t=3*2^m) :
    ∃ a : ℕ,3≤a ∧ q.exponent=1 ∧ q.prime=2^a-1 ∧
      Nat.Prime (2^a-1) ∧ m=e*a+t := by
  obtain ⟨a,ha,hm⟩ := binary_factor_of_degree_formula (q.order+1) e t m he hdegree
  obtain ⟨ha3,hex,hprime,hp⟩ := CFSGPSLTwoMersenneParameters.parameters q a hq ha
  exact ⟨a,ha3,hex,hprime,hp,hm⟩

/-- Consume the same correlated cover using only its retained binary degree
equation. There is no separately assumed field-successor or coprimality
condition; they follow from the degree equation and genuine prime-power data. -/
theorem correlated_binomial_orbits_of_binary_degree (q : CFSG.PrimePower)
    (m : ℕ) (hq : 4≤q.order)
    {J : Type} [Fintype J] [DecidableEq J] (he : 1≤Fintype.card J)
    (H : Subgroup (J → projectiveBorel (F := q.Field))) [H.Normal]
    (hindex : H.index=3) (hdegree : 3*(q.order+1)^Fintype.card J=3*2^m) :
    ∃ a : ℕ,3≤a ∧ q.exponent=1 ∧ Nat.Prime (2^a-1) ∧ m=Fintype.card J*a ∧
      IsSolvable (J → projectiveBorel (F := q.Field)) ∧
      ∃ index : MulAction.orbitRel.Quotient
          (J → projectiveBorel (F := q.Field)) (Cover H) ≃
          (Σ k : Fin (Fintype.card J+1),Fin ((Fintype.card J).choose k.val)),
        Nat.card (MulAction.orbitRel.Quotient
          (J → projectiveBorel (F := q.Field)) (Cover H))=2^Fintype.card J ∧
        ∀ o : MulAction.orbitRel.Quotient
          (J → projectiveBorel (F := q.Field)) (Cover H),
          Nat.card o.orbit=3*(2^a-1)^((index o).1.val) := by
  obtain ⟨a,ha,hm⟩ := binary_factor_of_degree_formula (q.order+1) (Fintype.card J) 0 m he
    (by simpa only [pow_zero,mul_one] using hdegree)
  obtain ⟨ha3,hex,_hprime,hp⟩ := CFSGPSLTwoMersenneParameters.parameters q a hq ha
  obtain ⟨_,_,hsol,index,hcount,hcards⟩ :=
    CFSGPSLTwoMersenneParameters.correlated_binomial_orbits q a hq ha H hindex
  exact ⟨a,ha3,hex,hp,by simpa only [add_zero] using hm,hsol,index,hcount,hcards⟩

end SymmetricSubgroupAsymptotics.TraceyExceptionalMersenneDegreeArithmetic
