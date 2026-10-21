import SymmetricSubgroupAsymptotics.BinaryPairSmallTopSectionOrders
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels
import SymmetricSubgroupAsymptotics.BinaryPairActualKernelDualSections
import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel
import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection

/-! Rank-five sources cannot have the full eight-dimensional pair kernel.
A seven-dimensional surviving section then has zero original denominator,
and the faithful large kernel has only the original constant central line. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive F.top.range (Fin 8)]

private theorem kernel_head_le_one_of_full
    (hU : IsPGroup 2 U) (hfull : F.kernelSpace = ⊤) :
    MarkedC4.normalGen F.top.ker ≤ 1 := by
  let S := F.axisSubrepresentation F.top.ker
  have hS : S.toSubmodule = ⊤ := F.ambientAxis_kernel.trans hfull
  let lift : (Fin 8 → ZMod 2) →ₗ[ZMod 2] S.toSubmodule := {
    toFun v := ⟨v, by rw [hS]; exact Submodule.mem_top⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let q := (Representation.Coinvariants.mk S.toRepresentation).comp lift
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨m, hm⟩ := Representation.Coinvariants.mk_surjective S.toRepresentation a
    exact ⟨m.val, hm⟩
  have ht : ∀ (g : F.top.range) (v : Fin 8 → ZMod 2),
      q (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 8) g v) = q v := by
    intro g v
    change Representation.Coinvariants.mk S.toRepresentation
      (S.toRepresentation g (lift v)) = Representation.Coinvariants.mk S.toRepresentation (lift v)
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [F.axis_normalGen_eq_coinvariants F.top.ker le_rfl hU]
  exact PermutationBinaryFourSection.trivial_quotient_finrank_le_one (0 : Fin 8) q hq ht

theorem kernel_finrank_le_seven_of_rank_five
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (htoprank : MarkedC4.genRank F.top.range ≤ 3) :
    Module.finrank (ZMod 2) F.kernelSpace ≤ 7 := by
  have hn : F.kernelSpace ≠ ⊤ := by
    intro hfull
    have hk := F.kernel_head_le_one_of_full hU hfull
    have hadd := F.genRank_le_actual_pair_kernel_add_top
    omega
  have hdim := Submodule.finrank_lt hn
  have hambient : Module.finrank (ZMod 2) (Fin 8 → ZMod 2) = 8 := by simp
  rw [hambient] at hdim
  omega

theorem original_center_le_two_of_large_kernel
    (hU : IsPGroup 2 U) (hlarge : 4 < Module.finrank (ZMod 2) F.kernelSpace) :
    Nat.card (Subgroup.center U) ≤ 2 := by
  let M := F.kernelTopPermutationSubrepresentation
  let q : M.toRepresentation.IntertwiningMap M.toRepresentation :=
    Representation.IntertwiningMap.id _
  have hinj : Function.Injective M.toRepresentation :=
    permutationSection_injective_of_half_lt (F.top_isPGroup hU) (0 : Fin 8)
      M.toRepresentation M q (fun v => ⟨v, rfl⟩) (by simpa using (show 8 < 2 * Module.finrank (ZMod 2) F.kernelSpace by omega))
  have hc := Nat.card_congr ((F.actualOriginalKernelChart).invariantsCenterEquiv
    F.top.rangeRestrict_surjective hinj)
  have hdim := PermutationBinaryFourSection.subrepresentation_invariants_le_one (0 : Fin 8) M
  calc
    Nat.card (Subgroup.center U) = Nat.card M.toRepresentation.invariants := hc.symm
    _ = 2 ^ Module.finrank (ZMod 2) M.toRepresentation.invariants := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M.toRepresentation.invariants))
    _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
    _ = 2 := by decide

theorem normal_eq_bot_of_section_seven
    (hU : IsPGroup 2 U) (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 7)
    (N : Subgroup U) [N.Normal]
    (hsection : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) = 7) : N = ⊥ := by
  have hd := (F.normalSpace N).finrank_quotient_add_finrank
  have hzero : Module.finrank (ZMod 2) (F.normalSpace N) = 0 := by omega
  have hbot : F.normalSpace N = ⊥ := Submodule.finrank_eq_zero.mp hzero
  have hN : N ≤ F.top.ker := F.normal_le_top_ker_of_large N hU (0 : Fin 8) (by simp only [Nat.card_fin]; omega)
  apply le_antisymm ?_ bot_le
  intro n hn
  apply Subgroup.mem_bot.mpr
  let k : F.top.ker := ⟨n, hN hn⟩
  have hv : (F.kernelSpaceHom k).toAdd ∈ F.normalSpace N :=
    ⟨Additive.ofMul (⟨k, hn⟩ : N.subgroupOf F.top.ker), rfl⟩
  have hv0 : (F.kernelSpaceHom k).toAdd = 0 := by simpa only [hbot, Submodule.mem_bot] using hv
  have he : F.kernelSpaceHom k = F.kernelSpaceHom 1 := by
    rw [map_one]
    exact congrArg Multiplicative.ofAdd hv0
  exact congrArg (fun z : F.top.ker => (z : U)) (F.kernelSpaceHom_bijective.1 he)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
