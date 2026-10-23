import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveOrderLower
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrderStrict

/-! Strict order growth of the actual original unitary central quotient,
using its actual nontrivial opposite Sylows. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGDisjointSylowProjectiveOrder

theorem twistedA_shifted_order_strict_lower (q : CFSG.PrimePower) (s : ℕ) :
    q.order ^ ((s + 3) * (s + 4)) < Nat.card (CFSG.Models.TwistedA (s + 3) q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  letI : Finite (Fixed (s + 3) q) := originalFixed_finite q (s + 3) (by omega)
  let D := commutator (Fixed (s + 3) q)
  let U := originalUnipotent (s + 3) q
  have hUD : U ≤ D := originalUnipotent_le_derived q s
  let P : Sylow q.prime D :=
    (originalSylow q (s + 3) (by omega)).subtype (originalSylow_le_derived q s)
  let w : D := ⟨originalReversal q (s + 3), originalReversal_mem_derived q s⟩
  let Q : Sylow q.prime D := P.mapSurjective (f := (MulAut.conj w).toMonoidHom)
    (MulAut.conj w).surjective
  have hPQ : (P : Subgroup D) ⊓ (Q : Subgroup D) = ⊥ := by
    apply bot_unique
    rintro x ⟨hx, hy⟩
    have hxU : x.val ∈ U := hx
    change x ∈ (P : Subgroup D).map (MulAut.conj w).toMonoidHom at hy
    obtain ⟨v, hv, hvx⟩ := hy
    have hxV : x.val ∈ originalOppositeUnipotent q (s + 3) :=
      ⟨v.val, hv, congrArg (fun z : D => z.val) hvx⟩
    have hxbot : x.val ∈ U ⊓ originalOppositeUnipotent q (s + 3) := ⟨hxU, hxV⟩
    rw [original_upper_inf_opposite q (s + 3) (by omega)] at hxbot
    change x = 1
    exact Subtype.ext hxbot
  have hcard : Nat.card P = q.order ^ ((s + 3) * (s + 4) / 2) :=
    (Nat.card_congr (U.subgroupOfEquivOfLe hUD).toEquiv).trans
      (original_unipotent_card q (s + 3) (by omega))
  have hq : 1 < q.order := lt_of_lt_of_le (by decide : 1 < 2)
    (q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime))
  have hexp : 0 < (s + 3) * (s + 4) / 2 := Nat.div_pos (by nlinarith) (by decide)
  have hnontriv : 1 < Nat.card P := by
    rw [hcard]
    simpa only [pow_zero] using pow_lt_pow_right₀ hq hexp
  have h := quotient_center_card_strict_lower P Q hPQ hnontriv
  rw [hcard, ← pow_mul] at h
  have he : ((s + 3) * (s + 4) / 2) * 2 = (s + 3) * (s + 4) := by
    have hs : s + 4 - 1 = s + 3 := by omega
    simpa only [Finset.sum_range_id, hs, Nat.mul_comm] using
      Finset.sum_range_id_mul_two (s + 4)
  rwa [he] at h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
