import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity
import SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import Mathlib.Data.Fintype.Perm

/-! A faithful six-point group without the prime five has order `2^a*3^b`,
hence is soluble by Burnside. An actual nonabelian full socle excludes this;
the remaining affine primitive alternative cannot have degree six. No
primitive-group or simple-group catalogue is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

private theorem sixPoint_twoPrimeOrder_receipt :
    ∀ n : Fin 721,n.val ∣ 720 → ¬5 ∣ n.val →
      ∃ a : Fin 5,∃ b : Fin 3,n.val=2^a.val*3^b.val := by decide +kernel

/-- Burnside applies to the actual group, using its faithful permutation
embedding rather than an order assigned to a catalogue row. -/
theorem isSolvable_of_faithful_degreeSix_not_five
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hX : Nat.card X=6) (hfive : ¬5 ∣ Nat.card G) :
    IsSolvable G := by
  have hd : Nat.card G ∣ 720 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom G X)
      (show Function.Injective (MulAction.toPermHom G X) from MulAction.toPerm_injective)
    simpa only [Nat.card_perm,hX] using h
  have hle : Nat.card G≤720 := Nat.le_of_dvd (by decide) hd
  obtain ⟨a,b,hab⟩ := sixPoint_twoPrimeOrder_receipt
    ⟨Nat.card G,by omega⟩ hd hfive
  exact burnsideTwoPrimeSolvability.solvable G 2 3 a.val b.val
    Nat.prime_two Nat.prime_three hab

namespace PrimitiveSocleRawStructure

/-- Projecting the actual full socle onto one of its simple factors
excludes solubility without any classification of that factor. -/
theorem NonaffineData.not_isSolvable
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) : ¬IsSolvable G := by
  intro hs
  letI : IsSolvable G := hs
  letI : IsSolvable (finiteGroupSocle G) := inferInstance
  let i : Fin D.factorCount := ⟨0,D.factorCount_pos⟩
  let f : finiteGroupSocle G →* D.Simple :=
    (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp
      D.socleEquiv.toMonoidHom
  have hf : Function.Surjective f := by
    intro t
    refine ⟨D.socleEquiv.symm (fun _ => t),?_⟩
    change D.socleEquiv (D.socleEquiv.symm (fun _ => t)) i=t
    rw [D.socleEquiv.apply_symm_apply]
  letI : IsSolvable D.Simple := solvable_of_surjective (f := f) hf
  exact D.noncommutative
    (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))

theorem NonaffineData.degreeSix_five_dvd_card
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hX : Nat.card X=6) :
    5 ∣ Nat.card G := by
  by_contra h
  exact D.not_isSolvable (isSolvable_of_faithful_degreeSix_not_five hX h)

end PrimitiveSocleRawStructure

/-- Every actual faithful primitive six-point group contains an element of
order five; the divisibility conclusion itself needs no finite locator. -/
theorem primitive_degreeSix_five_dvd_card_without_catalogue
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=6) : 5 ∣ Nat.card G := by
  let points : X≃Fin 6 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  letI : MulAction.IsPreprimitive S (Fin 6) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  have hS : 5 ∣ Nat.card S := by
    cases Classical.choice (PrimitiveSocleRawStructure.publishedONanScottStructure S (Fin 6)) with
    | inl D => exact D.degreeSix_five_dvd_card (by simp)
    | inr P =>
        let x : Fin 6 := 0
        have hp : P.p=2 := P.prime_eq_two_of_even_degree x (by decide)
        obtain ⟨d,hd⟩ := P.degree_eq_prime_power x
        rw [hp] at hd
        exact (PrimitiveSixExactProfileNormalGenerators.six_not_two_power d hd).elim
  rw [Nat.card_congr (faithfulLabelledActionEquiv points).toEquiv]
  exact hS

end SymmetricSubgroupAsymptotics
