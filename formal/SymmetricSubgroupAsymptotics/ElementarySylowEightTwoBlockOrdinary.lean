import SymmetricSubgroupAsymptotics.TwoBlockOddPointStabilizerOrdinary
import SymmetricSubgroupAsymptotics.ElementarySylowPointStabilizerOrder
import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators

/-! The actual imprimitive eight-point action with four-point minimal
component costs three generators when its actual Sylow two-subgroup is
elementary. Odd original stabilizers kill the true two-coordinate axis;
all component, block, and physical-point charts are inherited unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementarySylowEightTwoBlockOrdinary

variable (J : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive J (Fin 8)] {x₀ : Fin 8}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

theorem genRank_le_three (P : Sylow 2 J) (hel : ∀ g : P, g^2 = 1)
    (hr : Nat.card block.Fibre = 4) : MarkedC4.genRank J ≤ 3 := by
  letI : Nonempty block.Fibre := ⟨⟨x₀,block.map_base⟩⟩
  letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
  let S := OriginalBlockOrdinaryCompressionState.initialState J block
  let rho : J →* PermutationalWreathProduct block.Component block.Top block.Points := S.rho
  have hproduct : 4*Nat.card block.Points = 8 := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 2 := by omega
  let e : block.Fibre × block.Points ≃ Fin 8 :=
    ActualBlockWreathEmbedding.productEquiv block.map block.map_equivariant block.base
  have hcompat (a : J) (p : block.Fibre × block.Points) :
      e (rho a • p) = a • e p :=
    ActualBlockWreathEmbedding.productEquiv_equivariant
      block.map block.map_equivariant block.base a p
  have hodd (x : Fin 8) : ¬2 ∣ Nat.card (MulAction.stabilizer J x) :=
    ElementarySylowPointStabilizerOrder.two_not_dvd_stabilizer_card
      P hel 3 (by simp only [Nat.card_fin]; decide) x
  have hh := TwoBlockOddPointStabilizerOrdinary.genRank_le_local_add_top
    rho e hcompat ht S.rho_injective S.top_surjective S.fullComponent
      (by rw [hr]; decide) hodd
  have hlocal : MarkedC4.genRank block.Component ≤ 2 :=
    SmallFourPointOrdinaryGenerators.genRank_le_two hr
  have htopcard : Nat.card block.Top ≤ 2 := by
    have h := Nat.card_le_card_of_injective
      (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
    simpa only [Nat.card_perm,ht,show Nat.factorial 2 = 2 by decide] using h
  have htop : MarkedC4.genRank block.Top ≤ 1 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
      (by simpa only [pow_one] using htopcard)
  change MarkedC4.genRank J ≤ MarkedC4.genRank block.Component + MarkedC4.genRank block.Top at hh
  omega

end SymmetricSubgroupAsymptotics.ElementarySylowEightTwoBlockOrdinary
