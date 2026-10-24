import SymmetricSubgroupAsymptotics.External.CFSG.Parameters
import Mathlib.Tactic.NormNum

/-! A bounded prime-power arithmetic certificate, not an action census.
The three exceptional small field orders are retained literally; all
other admissible orders meet one of the shared native class budgets. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.RankOneRemainingParameterArithmetic

private theorem finite_parameters : ∀p:Fin 17,∀e:Fin 5,p.val.Prime→0<e.val→
    4≤p.val^e.val→p.val^e.val≤16→
    (p.val^e.val=4 ∨ p.val^e.val=5 ∨ p.val^e.val=9) ∨
      (p.val=2 ∧ 8≤p.val^e.val) ∨
      (p.val^e.val=7 ∨ p.val^e.val=11) ∨
      (p.val≠2 ∧ 13≤p.val^e.val) := by decide +kernel

theorem field_parameters (q : CFSG.PrimePower) (hlo : 4≤q.order) (hhi : q.order≤16) :
    (q.order=4 ∨ q.order=5 ∨ q.order=9) ∨
      (q.prime=2 ∧ 8≤q.order) ∨ (q.order=7 ∨ q.order=11) ∨
      (q.prime≠2 ∧ 13≤q.order) := by
  have hp : q.prime<17 := by
    have h := Nat.le_self_pow q.exponent_pos.ne' q.prime
    change q.prime ≤ q.order at h
    omega
  have he : q.exponent<5 := by
    by_contra h
    have hb := (Nat.pow_le_pow_left q.prime_isPrime.two_le 5).trans
      (Nat.pow_le_pow_right q.prime_isPrime.pos (by omega : 5≤q.exponent))
    change 2^5 ≤ q.order at hb
    norm_num at hb
    omega
  exact finite_parameters ⟨q.prime,hp⟩ ⟨q.exponent,he⟩ q.prime_isPrime
    q.exponent_pos hlo hhi

end SymmetricSubgroupAsymptotics.RankOneRemainingParameterArithmetic
