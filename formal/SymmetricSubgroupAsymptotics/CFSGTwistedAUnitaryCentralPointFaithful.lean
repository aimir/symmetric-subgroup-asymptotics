import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralPointAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveOrderLower
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness

/-! The actual central-point action of original unitary automorphisms
is faithful under the original simple-model hypothesis. The labelled
subgroup is nontrivial and proper by its proved q-element centre and
the actual Sylow/order comparison. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

theorem projectiveCentralRootLine_eq_map_center (q : CFSG.PrimePower) (s : ℕ) :
    projectiveCentralRootLine q s =
      (Subgroup.center (naturalUnipotent (s + 3) q)).map (unitaryProjectiveUpperHom q s) := by
  change (naturalCentralRootLine q (s + 1)).map (unitaryProjectiveCover q s) = _
  rw [naturalCentralRootLine_eq_center_image, Subgroup.map_map]
  rfl

theorem projectiveCentralRootLine_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (projectiveCentralRootLine q s) = q.order := by
  rw [projectiveCentralRootLine_eq_map_center,
    Subgroup.card_map_of_injective (unitaryProjectiveUpperHom_injective q s)]
  exact naturalUnipotent_center_card q (s + 1)

theorem projectiveCentralRootLine_ne_bot (q : CFSG.PrimePower) (s : ℕ) :
    projectiveCentralRootLine q s ≠ ⊥ := by
  intro he
  have hc := projectiveCentralRootLine_card q s
  rw [he, Subgroup.card_bot] at hc
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  omega

theorem projectiveCentralRootLine_ne_top (q : CFSG.PrimePower) (s : ℕ) :
    projectiveCentralRootLine q s ≠ ⊤ := by
  have hle : projectiveCentralRootLine q s ≤ (unitaryProjectiveUpperHom q s).range := by
    rw [projectiveCentralRootLine_eq_map_center]
    exact (Subgroup.center (naturalUnipotent (s + 3) q)).map_le_range _
  have hc : Nat.card (unitaryProjectiveUpperHom q s).range =
      q.order ^ ((s + 3) * (s + 4) / 2) := by
    exact (Nat.card_congr (MonoidHom.ofInjective
      (unitaryProjectiveUpperHom_injective q s)).toEquiv).symm.trans
        (naturalUnipotent_card q (s + 3))
  intro he
  have htop : (unitaryProjectiveUpperHom q s).range = ⊤ := by
    apply top_unique
    rwa [← he]
  rw [htop, Subgroup.card_top] at hc
  have ho := twistedA_shifted_order_lower q s
  rw [hc] at ho
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hn : 0 < (s + 3) * (s + 4) / 2 := by
    have hp : 12 ≤ (s + 3) * (s + 4) := by nlinarith
    omega
  have hpow : 2 ≤ q.order ^ ((s + 3) * (s + 4) / 2) :=
    hq.trans (Nat.le_self_pow (Nat.ne_of_gt hn) q.order)
  nlinarith

theorem unitaryCentralPointActionHom_injective (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)] :
    Function.Injective (unitaryCentralPointActionHom q s) := by
  let P : unitaryCentralPoints q s :=
    ⟨conjugateCentralPoint q (s + 1) 1, ⟨1, rfl⟩⟩
  have hbase : unitaryCentralPointLabel q s P = projectiveCentralRootLine q s := by
    rw [unitaryCentralPointLabel_representative q s P 1 rfl]
    change (projectiveCentralRootLine q s).map
      (MulAut.conj (unitaryProjectiveCover q s 1)).toMonoidHom = _
    simp only [map_one]
    exact Subgroup.map_id _
  apply CFSGSubgroupFamilyFaithfulness.permutationHom_injective
    (unitaryCentralPointLabel q s) (unitaryCentralPointLabel_injective q s)
    (unitaryCentralPointLabel_stable q s) P
  · rw [hbase]
    exact projectiveCentralRootLine_ne_bot q s
  · rw [hbase]
    exact projectiveCentralRootLine_ne_top q s

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
