import SymmetricSubgroupAsymptotics.BinaryStructuredEpiFibre
import SymmetricSubgroupAsymptotics.PGroupDerivedNormalSubgroupCount

/-! The structured epimorphism estimate for one fixed original source
tuple. We sum its exact normal-kernel fibres inside the original derived
subgroup. Every map whose tuple image generates the target is retained.
The tuple need not generate the source, and its length only affects a
target-dependent constant. Source tuple selection is a separate step.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

local instance structuredTupleHomFinite {G Q : Type*} [Group G] [Group Q]
    [Finite G] [Finite Q] : Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

/-- For a fixed tuple, the only source-dependent exponential factors are
the center order to the original binary character rank and the derived
order to the original derived-normal relative rank. No source nilpotency
class bound, source generator number, or class-count input is assumed. -/
theorem binaryStructured_tuple_image_generating_card_le
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    {ι : Type*} [Finite ι] (x : ι → G)
    (hG : IsPGroup 2 G) (hQ : IsPGroup 2 Q) :
    Nat.card {f : G →* Q // Subgroup.closure (Set.range (f ∘ x)) = ⊤} ≤
      (Nat.card (commutator Q))^(primeDerivedNormalRank 2 G) *
        ((Nat.card Q)^((Nat.card (commutator Q))^(Nat.card ι)) *
          (Nat.card (Subgroup.center Q))^(binaryCharacterRank G)) := by
  let D := generatorNormalCommutator x
  let F := {f : G →* Q // Subgroup.closure (Set.range (f ∘ x)) = ⊤}
  let T := NormalSubgroupsAtMostIndex D (Nat.card (commutator Q))
  let c := (Nat.card Q)^((Nat.card (commutator Q))^(Nat.card ι)) *
    (Nat.card (Subgroup.center Q))^(binaryCharacterRank G)
  have hindex (f : F) : (D ⊓ f.1.ker).relIndex D = Nat.card (commutator Q) := by
    rw [Subgroup.inf_relIndex_left,D.relIndex_ker]
    exact congrArg (fun S : Subgroup Q => Nat.card S)
      (generatorNormalCommutator_map_of_generating x f.1 f.2)
  let π : F → T := fun f =>
    ⟨D ⊓ f.1.ker,inferInstance,inf_le_left,(hindex f).le⟩
  have hfibre (H : T) : Nat.card {f : F // π f = H} ≤ c := by
    letI : H.1.Normal := H.2.1
    let K := {f : G →* Q // Subgroup.closure (Set.range (f ∘ x)) = ⊤ ∧
      generatorNormalCommutator x ⊓ f.ker = H.1}
    let j : {f : F // π f = H} → K := fun f =>
      ⟨f.1.1,f.1.2,congrArg (fun t : T => t.1) f.2⟩
    have hj : Function.Injective j := by
      intro f g he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : K => t.1) he
    exact (Nat.card_le_card_of_injective j hj).trans
      (BinaryStructuredEpiFibre.kernel_fibre_card_le x H.1 hQ)
  have hnormal : Nat.card T ≤
      (Nat.card (commutator Q))^(primeDerivedNormalRank 2 G) := by
    obtain ⟨a,ha⟩ := (hQ.to_subgroup (commutator Q)).exists_card_eq
    change Nat.card (NormalSubgroupsAtMostIndex D (Nat.card (commutator Q))) ≤ _
    rw [ha,← pow_mul]
    exact pGroup_derived_normal_subgroup_count_le hG D
      (generatorNormalCommutator_le_derived x) a
  letI : Fintype T := Fintype.ofFinite T
  calc
    Nat.card F = Nat.card (Σ H : T, {f : F // π f = H}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = ∑ H : T, Nat.card {f : F // π f = H} := Nat.card_sigma
    _ ≤ ∑ _H : T, c := Finset.sum_le_sum (fun H _ => hfibre H)
    _ = Nat.card T * c := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      rfl
    _ ≤ _ := Nat.mul_le_mul_right c hnormal

end SymmetricSubgroupAsymptotics
