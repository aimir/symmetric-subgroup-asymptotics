import SymmetricSubgroupAsymptotics.BinaryKernelFourDivisorOrdinary
import SymmetricSubgroupAsymptotics.ElementarySylowTransitiveOrderObstruction
import SymmetricSubgroupAsymptotics.TwoBlockWreathNormalGenerators
import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators

/-! In the actual eight-point action with a binary minimal block, an
elementary Sylow two-subgroup leaves a kernel of order at most two above
the actual four-point top. This uses original source divisibility and
literal faithful kernel coordinates, with no A4/S4 recognition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementarySylowEightBinaryBlockOrdinary
open TwoBlockWreathNormalGenerators

variable (J : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive J (Fin 8)] {x₀ : Fin 8}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

theorem genRank_le_three (P : Sylow 2 J) (hel : ∀ g : P, g^2 = 1)
    (hr : Nat.card block.Fibre = 2) : MarkedC4.genRank J ≤ 3 := by
  let S := OriginalBlockOrdinaryCompressionState.initialState J block
  let f := top S.rho
  have hproduct : 2*Nat.card block.Points = 8 := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 4 := by omega
  have hlocalcard : Nat.card block.Component ∣ 2 := by
    have h := Subgroup.card_dvd_of_injective block.Component.subtype block.Component.subtype_injective
    simpa only [Nat.card_perm,hr,show Nat.factorial 2 = 2 by decide] using h
  have hlocalSquare (a : block.Component) : a^2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard a).trans hlocalcard)
  have hker : IsPGroup 2 f.ker := by
    intro x
    refine ⟨1,?_⟩
    rw [pow_one]
    apply coordinates_joint_injective S.rho S.rho_injective
    funext i
    simpa only [map_pow,map_one] using hlocalSquare (coordinate S.rho i x)
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  have hfour : 4 ∣ Nat.card block.Top := by
    rw [←ht,←MulAction.index_stabilizer_of_transitive block.Top block.base]
    exact Subgroup.index_dvd_card _
  have hnot16 : ¬16 ∣ Nat.card J :=
    ElementarySylowTransitiveOrderObstruction.sixteen_not_dvd_card_of_degree_eight
      (X := Fin 8) P hel (by simp only [Nat.card_fin])
  have hh := BinaryKernelFourDivisorOrdinary.genRank_le_one_add_quotient
    f S.top_surjective hker hfour hnot16
  change MarkedC4.genRank J ≤ 1 + MarkedC4.genRank block.Top at hh
  have htop : MarkedC4.genRank block.Top ≤ 2 :=
    SmallFourPointOrdinaryGenerators.genRank_le_two ht
  omega

end SymmetricSubgroupAsymptotics.ElementarySylowEightBinaryBlockOrdinary
