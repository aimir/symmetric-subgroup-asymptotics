import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixRecognition
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding

/-! Elementary order and normal-subgroup constraints inside the actual
symmetric group S6. These are coset-action and normal-lattice arguments,
not a list of primitive permutation groups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open PrimitiveDegreeSixRecognition

/-- A proper small-order subgroup of S6 has trivial normal core. -/
theorem sixPoint_normalCore_eq_bot_of_card_lt
    (H : Subgroup (Equiv.Perm (Fin 6))) (hH : Nat.card H<360) : H.normalCore=⊥ := by
  by_contra hn
  have hn' : Nontrivial H.normalCore := H.normalCore.nontrivial_iff_ne_bot.mpr hn
  have hA : alternatingGroup (Fin 6)≤H :=
    (Equiv.Perm.alternatingGroup_le_of_normal (by simp) hn').trans H.normalCore_le
  have hc := Subgroup.card_le_of_le hA
  rw [card_alt_six] at hc
  omega

/-- Index three or four would faithfully represent S6 on too few points. -/
theorem sixPoint_subgroup_card_ne_180_240
    (H : Subgroup (Equiv.Perm (Fin 6))) : Nat.card H≠180 ∧ Nat.card H≠240 := by
  constructor <;> intro hH
  all_goals
    have hc : H.normalCore=⊥ := sixPoint_normalCore_eq_bot_of_card_lt H (by omega)
    have hf : Function.Injective
        (MulAction.toPermHom (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 6)⧸H)) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [←Subgroup.normalCore_eq_ker H,hc]
    have hb := Nat.card_le_card_of_injective _ hf
    rw [card_perm_six,Nat.card_perm,←H.index_eq_card] at hb
    have hm := H.card_mul_index
    rw [hH,card_perm_six] at hm
  · have hi : H.index=4 := by omega
    rw [hi] at hb
    norm_num [Nat.factorial] at hb
  · have hi : H.index=3 := by omega
    rw [hi] at hb
    norm_num [Nat.factorial] at hb

/-- A normal subgroup in a faithful six-point group of order360 or720
has order at least360, using the actual A6/S6 normal lattice. -/
theorem faithfulSix_largeOrder_normal_card_ge
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)]
    (hG : Nat.card G=360 ∨ Nat.card G=720)
    (N : Subgroup G) [N.Normal] (hN : N≠⊥) : 360≤Nat.card N := by
  let f := MulAction.toPermHom G (Fin 6)
  have hf : Function.Injective f := MulAction.toPerm_injective
  let H := f.range
  let e : G≃*H := MonoidHom.ofInjective hf
  have hH : Nat.card H=Nat.card G := (Nat.card_congr e.toEquiv).symm
  rcases hG with hG|hG
  · have hi : H.index=2 := by
      have hm := H.card_mul_index
      rw [hH,hG,card_perm_six] at hm
      omega
    have heH : H=alternatingGroup (Fin 6) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    let eA : G≃*alternatingGroup (Fin 6) := e.trans (MulEquiv.subgroupCongr heH)
    let M := N.map eA.toMonoidHom
    letI : M.Normal := (inferInstance : N.Normal).map eA.toMonoidHom eA.surjective
    have hM : M≠⊥ := by
      intro hm
      have hle := (Subgroup.map_eq_bot_iff (H := N)).mp hm
      have hk : eA.toMonoidHom.ker=⊥ := (MonoidHom.ker_eq_bot_iff _).mpr eA.injective
      exact hN (le_antisymm (hle.trans hk.le) bot_le)
    letI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have htop : M=⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal M inferInstance).resolve_left hM
    have hc : Nat.card M=Nat.card N :=
      (Nat.card_congr (N.equivMapOfInjective eA.toMonoidHom eA.injective).toEquiv).symm
    rw [htop,Subgroup.card_top,card_alt_six] at hc
    omega
  · have htop : H=⊤ := by
      apply Subgroup.eq_of_le_of_card_ge (show H≤⊤ from le_top)
      rw [Subgroup.card_top,card_perm_six,hH,hG]
    have hs : Function.Surjective f := MonoidHom.range_eq_top.mp htop
    let M := N.map f
    letI : M.Normal := (inferInstance : N.Normal).map f hs
    have hM : M≠⊥ := by
      intro hm
      have hle := (Subgroup.map_eq_bot_iff (H := N)).mp hm
      have hk : f.ker=⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hf
      exact hN (le_antisymm (hle.trans hk.le) bot_le)
    have hn : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM
    have hA : alternatingGroup (Fin 6)≤M :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp) hn
    have hb := Subgroup.card_le_of_le hA
    have hc : Nat.card M=Nat.card N :=
      (Nat.card_congr (N.equivMapOfInjective f hf).toEquiv).symm
    simpa only [card_alt_six,hc] using hb

end SymmetricSubgroupAsymptotics
