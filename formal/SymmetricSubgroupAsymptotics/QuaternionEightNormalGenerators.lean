import SymmetricSubgroupAsymptotics.MetacyclicNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-! The actual quaternion complement has a cyclic kernel and cyclic
quotient. Every normal subgroup therefore needs two generators, without
normal enumeration or a split presentation. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.QuaternionEightNormalGenerators
open QuaternionGroup
abbrev Q8 := QuaternionGroup 2
abbrev Bit := Multiplicative (ZMod 2)

def parity : Q8 →* Bit where
  toFun
    | .a _ => Multiplicative.ofAdd 0
    | .xa _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · change Multiplicative.ofAdd (0 : ZMod 2)=Multiplicative.ofAdd (1+1)
      congr 1

theorem parity_ker : parity.ker=Subgroup.zpowers (a (1 : ZMod 4) : Q8) := by
  apply le_antisymm
  · intro q hq
    cases q with
    | a i =>
      have hp : (a (1 : ZMod 4) : Q8)^i.val=a i := by
        rw [a_one_pow,ZMod.natCast_zmod_val]
      rw [← hp]
      exact Subgroup.npow_mem_zpowers _ _
    | xa i =>
      have hqeq : parity (.xa i)=1 := MonoidHom.mem_ker.mp hq
      have he : (1 : ZMod 2)=0 := congrArg Multiplicative.toAdd hqeq
      exact ((by decide : (1 : ZMod 2)≠0) he).elim
  · apply Subgroup.zpowers_le.mpr
    rfl

instance : IsCyclic parity.ker := by
  rw [parity_ker]
  infer_instance

theorem normal_generating_pairs :
    ∀ N : Subgroup Q8, N.Normal →
      ∃ x : Fin 2 → Q8, Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_pairs_of_cyclic_kernel parity

theorem normalGen_le_two (N : Subgroup Q8) [N.Normal] : MarkedC4.normalGen N≤2 := by
  obtain ⟨x,hx⟩ := normal_generating_pairs N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle_two (N : Subgroup Q8) [N.Normal] :
    SocleNormalGeneratorBound (Q8 ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples normal_generating_pairs N

theorem coprime_three : Nat.Coprime 3 (Nat.card Q8) := by
  rw [Nat.card_eq_fintype_card,QuaternionGroup.card]
  decide

end SymmetricSubgroupAsymptotics.QuaternionEightNormalGenerators
