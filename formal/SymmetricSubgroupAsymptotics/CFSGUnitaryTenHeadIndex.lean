import SymmetricSubgroupAsymptotics.UnitaryTenHeadScaledFrameNumerics
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryAdmissibleIndexLower
import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreePauliIndex

/-! All ten proper-index floors are proved for the SAME actual unitary
models in the numerical parameter family. The rank-two floors use its
actual coupled radical/torus trichotomy; field powers, ternary coupling,
higher binary coupling and the faithful Pauli27 supply the other floors.
There is no supplied numerical index or model-recognition hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadIndex
open CFSGTwistedAUnitaryCoordinates UnitaryTenHeadScaledFrameNumerics

private theorem prime_of_prime_order (q : CFSG.PrimePower) (p : ℕ)
    (hp : p.Prime) (hq : q.order=p) : q.prime=p :=
  (Nat.Prime.pow_inj' q.prime_isPrime hp q.exponent_pos.ne'
    (by decide : (1 : ℕ)≠0) (show q.prime^q.exponent=p^1 by simpa only [pow_one] using hq)).1

theorem proper_index_floor (j : Fin 10) (q : CFSG.PrimePower)
    (hq : q.order=(parameters j).2)
    [hSimple : IsSimpleGroup (CFSG.Models.TwistedA (parameters j).1 q)]
    (H : Subgroup (CFSG.Models.TwistedA (parameters j).1 q)) (hH : H≠⊤) :
    indexFloor j ≤ H.index := by
  fin_cases j
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := by
      simpa [parameters] using hSimple
    change q.order=3 at hq
    change 27≤H.index
    have hp : q.prime=3 := prime_of_prime_order q 3 (by decide) hq
    have hbound : q.order^3≤H.index ∨
        q.prime^2*q.order*(q.order-1)≤H.index ∨
          q.prime*q.order*(q.order+1)≤(q.order+1).gcd 3*H.index :=
      twistedA_rankTwo_coupled_proper_index q (by rw [hq]) H hH
    rcases hbound with h | h | h <;> norm_num [hq,hp] at h <;> omega
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := by
      simpa [parameters] using hSimple
    change q.order=4 at hq
    change 40≤H.index
    have hp : q.prime=2 := (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two
      q.exponent_pos.ne' (by decide : (2 : ℕ)≠0)
      (show q.prime^q.exponent=2^2 from hq)).1
    have hbound : q.order^3≤H.index ∨
        q.prime^2*q.order*(q.order-1)≤H.index ∨
          q.prime*q.order*(q.order+1)≤(q.order+1).gcd 3*H.index :=
      twistedA_rankTwo_coupled_proper_index q (by rw [hq]; decide) H hH
    rcases hbound with h | h | h <;> norm_num [hq,hp] at h <;> omega
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := by
      simpa [parameters] using hSimple
    change q.order=5 at hq
    change 50≤H.index
    have hp : q.prime=5 := prime_of_prime_order q 5 (by decide) hq
    have hbound : q.order^3≤H.index ∨
        q.prime^2*q.order*(q.order-1)≤H.index ∨
          q.prime*q.order*(q.order+1)≤(q.order+1).gcd 3*H.index :=
      twistedA_rankTwo_coupled_proper_index q (by rw [hq]; decide) H hH
    rcases hbound with h | h | h <;> norm_num [hq,hp] at h <;> omega
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := by
      simpa [parameters] using hSimple
    change q.order=7 at hq
    change 343≤H.index
    have hp : q.prime=7 := prime_of_prime_order q 7 (by decide) hq
    have hbound : q.order^3≤H.index ∨
        q.prime^2*q.order*(q.order-1)≤H.index ∨
          q.prime*q.order*(q.order+1)≤(q.order+1).gcd 3*H.index :=
      twistedA_rankTwo_coupled_proper_index q (by rw [hq]; decide) H hH
    rcases hbound with h | h | h <;> norm_num [hq,hp] at h <;> omega
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := by
      simpa [parameters] using hSimple
    change q.order=8 at hq
    change 64≤H.index
    have h := twistedA_admissible_field_power_le_proper_index 2 (by decide) q
      (by intro _; omega) H hH
    simpa only [hq,Nat.reducePow] using h
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := by
      simpa [parameters] using hSimple
    change q.order=9 at hq
    change 270≤H.index
    have hp : q.prime=3 := (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
      q.exponent_pos.ne' (by decide : (2 : ℕ)≠0)
      (show q.prime^q.exponent=3^2 from hq)).1
    have hbound : q.order^3≤H.index ∨
        q.prime^2*q.order*(q.order-1)≤H.index ∨
          q.prime*q.order*(q.order+1)≤(q.order+1).gcd 3*H.index :=
      twistedA_rankTwo_coupled_proper_index q (by rw [hq]; decide) H hH
    rcases hbound with h | h | h <;> norm_num [hq,hp] at h <;> omega
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := by
      simpa [parameters] using hSimple
    change q.order=2 at hq
    change 27≤H.index
    exact CFSGUnitaryBinaryRankThreePauliIndex.proper_index_ge_twentySeven q hq H hH
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := by
      simpa [parameters] using hSimple
    change q.order=3 at hq
    change 48≤H.index
    exact twistedA_rankThree_ternary_coupled_proper_index q hq H hH
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := by
      simpa [parameters] using hSimple
    change q.order=4 at hq
    change 64≤H.index
    simpa only [hq,Nat.reducePow] using
      twistedA_higher_field_power_le_proper_index 3 (by decide) q H hH
  · letI : IsSimpleGroup (CFSG.Models.TwistedA 4 q) := by
      simpa [parameters] using hSimple
    change q.order=2 at hq
    change 48≤H.index
    have hp : q.prime=2 := prime_of_prime_order q 2 Nat.prime_two hq
    simpa only [hq,hp,Nat.reducePow,Nat.reduceSub,Nat.reduceMul] using
      twistedA_higher_coupled_proper_index 4 (by decide) q H hH

end SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadIndex
