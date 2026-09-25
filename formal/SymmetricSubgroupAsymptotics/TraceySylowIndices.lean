import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Actual Sylow-stabilizer indices for the induced-module envelope.
Every subgroup is allowed, in particular each original conjugate point
stabilizer. No normality or split extension is assumed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

theorem traceySylow_relative_valuation (P : Sylow p G) (H : Subgroup G) :
    H.index.factorization p≤(H.relIndex (P:Subgroup G)).factorization p := by
  have hdiv : H.index∣H.relIndex (P:Subgroup G)*(P:Subgroup G).index := by
    rw [← Subgroup.inf_relIndex_right H (P:Subgroup G),
      Subgroup.relIndex_mul_index inf_le_right]
    exact Subgroup.index_dvd_of_le inf_le_left
  have hH : H.index≠0 := H.index_ne_zero_of_finite
  have hP : (P:Subgroup G).index≠0 := (P:Subgroup G).index_ne_zero_of_finite
  have hlocal : H.relIndex (P:Subgroup G)≠0 :=
    (H.subgroupOf (P:Subgroup G)).index_ne_zero_of_finite
  have hv := (Nat.factorization_le_iff_dvd hH (mul_ne_zero hlocal hP)).mpr hdiv p
  simpa [Nat.factorization_mul hlocal hP,
    Nat.factorization_eq_zero_of_not_dvd P.not_dvd_index] using hv

/-- The local index is an actual prime power whose exponent is at least
the valuation of the original global index. -/
theorem traceySylow_relative_index (P : Sylow p G) (H : Subgroup G) :
    ∃ j : ℕ,H.relIndex (P:Subgroup G)=p^j ∧ H.index.factorization p≤j := by
  obtain ⟨j,hj⟩ := P.isPGroup'.index (H.subgroupOf (P:Subgroup G))
  refine ⟨j,hj,?_⟩
  have hv := traceySylow_relative_valuation p P H
  change H.index.factorization p≤(H.subgroupOf (P:Subgroup G)).index.factorization p at hv
  rw [hj,Nat.factorization_pow_self (Fact.out : p.Prime)] at hv
  exact hv

/-- Every actual Sylow orbit of a finite transitive action has the
required valuation, with its literal point stabilizer retained. -/
theorem traceySylow_orbit_card {X : Type*} [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X] (P : Sylow p G) (x : X) :
    ∃ j : ℕ,(MulAction.orbit P x).ncard=p^j ∧ (Nat.card X).factorization p≤j := by
  obtain ⟨j,hj,hv⟩ := traceySylow_relative_index p P (MulAction.stabilizer G x)
  have hstab : (MulAction.stabilizer G x).subgroupOf (P:Subgroup G)=
      MulAction.stabilizer P x := by
    ext g
    rfl
  rw [Subgroup.relIndex,hstab,MulAction.index_stabilizer] at hj
  rw [MulAction.index_stabilizer_of_transitive] at hv
  exact ⟨j,hj,hv⟩

/-- The exponents of all actual Sylow orbits have the common lower
valuation and their prime powers sum to the entire original degree. -/
theorem traceySylow_orbit_degrees {X : Type*} [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X] (P : Sylow p G)
    [Fintype (MulAction.orbitRel.Quotient P X)] :
    ∃ j : MulAction.orbitRel.Quotient P X→ℕ,
      (∀o,(Nat.card X).factorization p≤j o) ∧
      (∀o,(MulAction.orbit P o.out).ncard=p^j o) ∧
      ∑o,p^j o=Nat.card X := by
  classical
  choose j hj hv using fun o : MulAction.orbitRel.Quotient P X =>
    traceySylow_orbit_card p P o.out
  refine ⟨j,hv,hj,?_⟩
  calc
    ∑o,p^j o=∑o:MulAction.orbitRel.Quotient P X,Nat.card (MulAction.orbit P o.out) := by
      apply Finset.sum_congr rfl
      intro o _
      rw [Nat.card_coe_set_eq,hj]
    _=Nat.card X := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (MulAction.selfEquivSigmaOrbits P X).symm

/-- The number of original Sylow orbits times the prime part of the
degree is at most the whole degree. This is also the coprime-Sylow
numerical input for the semisimple induced-module branch. -/
theorem traceySylow_orbit_count {X : Type*} [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X] (P : Sylow p G)
    [Fintype (MulAction.orbitRel.Quotient P X)] :
    Fintype.card (MulAction.orbitRel.Quotient P X)*p^(Nat.card X).factorization p≤
      Nat.card X := by
  obtain ⟨j,hj,_,hs⟩ := traceySylow_orbit_degrees p P (X:=X)
  calc
    _=∑o:MulAction.orbitRel.Quotient P X,p^(Nat.card X).factorization p := by simp
    _≤∑o,p^j o := Finset.sum_le_sum fun o _ =>
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (hj o)
    _=Nat.card X := hs

end SymmetricSubgroupAsymptotics
