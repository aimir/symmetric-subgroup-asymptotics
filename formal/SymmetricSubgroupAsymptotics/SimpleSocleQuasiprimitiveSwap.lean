import SymmetricSubgroupAsymptotics.QuasiprimitiveSwapRecognition
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor

/-! The original one-factor full socle is contained in every nontrivial
normal subgroup. Its actual transitivity therefore proves quasiprimitivity,
without silently adding primitivity to the raw nonaffine data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
open PrimitiveSocleRawStructure MulAction

theorem oneFactor_quasiPreprimitive {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] (D : NonaffineData G X) (hk : D.factorCount=1) :
    MulAction.IsQuasiPreprimitive G X := by
  letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.socle_transitive
  refine { exists_smul_eq := ?_, isPretransitive_of_normal := ?_ }
  · intro x y
    obtain ⟨s,hs⟩ := MulAction.exists_smul_eq (finiteGroupSocle G) x y
    exact ⟨s.val,hs⟩
  · intro N hN hfixed
    have hNne : N≠⊥ := by
      intro hbot
      apply hfixed
      rw [hbot]
      ext x
      simp only [Set.mem_univ,iff_true]
      apply MulAction.mem_fixedPoints.mpr
      intro n
      have hn : n.val=1 := Subgroup.mem_bot.mp n.property
      change (n.val : G) • x=x
      rw [hn,one_smul]
    have hle := D.oneFactor_socle_le hk N hN hNne
    constructor
    intro x y
    obtain ⟨s,hs⟩ := MulAction.exists_smul_eq (finiteGroupSocle G) x y
    exact ⟨⟨s.val,hle s.property⟩,hs⟩

theorem permutation_eq_top_of_single_factor_of_isSwap {X : Type}
    [Finite X] [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (D : NonaffineData P X) (hk : D.factorCount=1)
    (t : Equiv.Perm X) (ht : t.IsSwap) (htP : t∈P) : P=⊤ := by
  letI : MulAction.IsQuasiPreprimitive P X := oneFactor_quasiPreprimitive D hk
  exact QuasiprimitiveSwapRecognition.eq_top_of_isSwap_mem P t ht htP

end SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
