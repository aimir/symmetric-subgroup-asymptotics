import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeDisjoint
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalSylow
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrder
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The actual original unitary central quotient has at least the
square of its literal upper Sylow's order. No group-order formula,
model recognition, or assumption about the centre is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGDisjointSylowProjectiveOrder

theorem original_unipotent_card (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    Nat.card (originalUnipotent r q) = q.order ^ (r * (r + 1) / 2) := by
  have hc : Nat.card (originalUnipotent r q) = Nat.card (naturalUnipotent r q) :=
    (Nat.card_congr (MonoidHom.ofInjective
      (unipotentToOriginalFixed_injective r hr q)).toEquiv).symm
  exact hc.trans (naturalUnipotent_card q r)

theorem twistedA_shifted_order_lower (q : CFSG.PrimePower) (s : ℕ) :
    (q.order ^ ((s + 3) * (s + 4) / 2)) ^ 2 ≤ Nat.card (CFSG.Models.TwistedA (s + 3) q) := by
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
  have hcard : Nat.card P = q.order ^ ((s + 3) * (s + 4) / 2) := by
    have he : Nat.card P = Nat.card U :=
      Nat.card_congr (U.subgroupOfEquivOfLe hUD).toEquiv
    exact he.trans (original_unipotent_card q (s + 3) (by omega))
  have h := quotient_center_card_lower P Q hPQ
  rw [hcard] at h
  exact h

theorem twistedA_shifted_order_lower_exp (q : CFSG.PrimePower) (s : ℕ) :
    q.order ^ ((s + 3) * (s + 4)) ≤ Nat.card (CFSG.Models.TwistedA (s + 3) q) := by
  have h := twistedA_shifted_order_lower q s
  have he : ((s + 3) * (s + 4) / 2) * 2 = (s + 3) * (s + 4) := by
    have hs : s + 4 - 1 = s + 3 := by omega
    simpa only [Finset.sum_range_id, hs, Nat.mul_comm] using
      Finset.sum_range_id_mul_two (s + 4)
  rwa [← pow_mul, he] at h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
