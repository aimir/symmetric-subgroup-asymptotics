import SymmetricSubgroupAsymptotics.PermutationSubrepresentationSeparation
import SymmetricSubgroupAsymptotics.BinaryRegularFourSpaceSeparates
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopLargeKernel
import SymmetricSubgroupAsymptotics.BinarySixteenSmallDerivedJoint
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3

/-! The actual four-dimensional regular kernel separates points, so its
original extension has centre at most two even at the half-dimension
boundary. Its128-element source of rank at least six then has joint
source capacity four. The extension is arbitrary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance regular46SourceJointPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))
include E

theorem original_center_le_two_of_regular_four_space
    (hK : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart46.space) :
    Nat.card (Subgroup.center U)≤2 := by
  letI : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  let M := E.kernelTopPermutationSubrepresentation
  have hsep : ∀ x y : Fin 8,
      (∀ v : Fin 8 → ZMod 2,v∈M.toSubmodule → v x=v y) → x=y := by
    intro x y hh
    apply BinaryRegularFourSpaceSeparates.separates x y
    intro v hv
    exact hh v (by change v∈E.kernelSpace;rw [hK];exact hv)
  have hfaith : Function.Injective M.toRepresentation :=
    permutationSubrepresentation_injective_of_separating M hsep
  have hc := Nat.card_congr ((E.actualOriginalKernelChart).invariantsCenterEquiv
    E.top.rangeRestrict_surjective hfaith)
  have hd := PermutationBinaryFourSection.subrepresentation_invariants_le_one (0 : Fin 8) M
  calc
    Nat.card (Subgroup.center U)=Nat.card M.toRepresentation.invariants := hc.symm
    _ = 2^Module.finrank (ZMod 2) M.toRepresentation.invariants := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M.toRepresentation.invariants))
    _ ≤ 2^1 := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hd
    _ = 2 := by decide

theorem regular46_rank_six_source_joint_le_four
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart46.space) :
    Nat.card (commutator U)*Nat.card (Subgroup.center U)≤4 := by
  have hk : Nat.card E.kernelSpace=16 := by
    rw [hK,BinaryRegularEightNaturalRegistry.chart46.card]
    decide
  have ht : Nat.card E.top.range=8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
  have hu := E.kernelSpace_card_mul_top
  rw [hk,ht] at hu
  have hAb : 64≤Nat.card (Abelianization U) :=
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hh := (commutator U).card_mul_index
  change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
  have hd : Nat.card (commutator U)≤2 := by nlinarith
  exact (Nat.mul_le_mul hd (E.original_center_le_two_of_regular_four_space hK)).trans (by norm_num)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
