import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualClassCount
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassCubeSquareProperGap
import SymmetricSubgroupAsymptotics.SmallFibreNonaffineClassPacketResidual
import SymmetricSubgroupAsymptotics.SmallFibreSeventyFiveClassEnvelope
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Closed class consumers for the SAME actual M12 simple factor.
The proved class ceiling15 and actual outer ceiling5 are retained
separately. The binary one-factor branch uses the unsigned nonsplit
kernel reserve and actual top order; it does not replace Out by a looser
class budget or require the insufficient generic24B^3 scalar packet.
Both original degree forms and arbitrary actual subnormal sources remain.
No class, outer, capacity or bounded-degree callback is an endpoint input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCompleteClassConsumers
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction
open CFSG.Models.Presentations.M12

private theorem component_class_budget [IsSimpleGroup Model] :
    Nat.card (ConjClasses Model) * Nat.card (Outer Model) ≤ 75 :=
  Nat.mul_le_mul CFSGMathieuTwelveActualClassCount.class_card_le_fifteen
    CFSGMathieuTwelveOuterBound.outer_card_le_five

private theorem component_cube [IsSimpleGroup Model] :
    (Nat.card (ConjClasses Model) * Nat.card (Outer Model)) ^ 3 ≤ 5 ^ (11 - 1) :=
  (Nat.pow_le_pow_left component_class_budget 3).trans (by decide)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem primitive_subnormal_class_cube (D : NonaffineData G X)
    (e : D.Simple ≃* Model) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  letI : Finite Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  apply D.subnormal_class_cube_le_of_model_capacity Model e 11 (by decide)
    CFSGMathieuTwelveOuterBudgetOfFixedCapacity.proper_index_ge_eleven component_cube ?_ H hH
  rw [CFSGMathieuTwelveActualEquivalence.card]
  decide

theorem proper_subnormal_class_cube_gap (D : NonaffineData G X)
    (e : D.Simple ≃* Model) (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  letI : Finite Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  apply D.proper_subnormal_class_cube_le_of_model_square_capacity Model e 11 (by decide)
    CFSGMathieuTwelveOuterBudgetOfFixedCapacity.proper_index_ge_eleven component_cube ?_ H hH hne
  rw [CFSGMathieuTwelveActualEquivalence.card]
  decide

theorem original_small_fibre_subnormal_gap
    {A Ω Y : Type} [Group A] [MulAction A Ω] [MulAction A Y]
    [Finite A] [Finite Ω] [Finite Y] [FaithfulSMul A Ω]
    (π : Ω → Y) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ y, Nat.card (originalBlockFibre π y) = c)
    (E : NonaffineData (Top (A := A) (X := Y)) Y)
    (e : E.Simple ≃* Model) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  letI : Finite Model := Finite.of_equiv E.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  let B := Nat.card (ConjClasses E.Simple) * Nat.card (Outer E.Simple)
  have hclass : Nat.card (ConjClasses E.Simple) ≤ 15 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans
        CFSGMathieuTwelveActualClassCount.class_card_le_fifteen
  have houter : Nat.card (Outer E.Simple) ≤ 5 := by
    rw [outer_card_congr e]
    exact CFSGMathieuTwelveOuterBound.outer_card_le_five
  have hB : B ≤ 75 := Nat.mul_le_mul hclass houter
  have hcardS : Nat.card E.Simple = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSGMathieuTwelveActualEquivalence.card
  have hindex : ∀ K : Subgroup E.Simple, K ≠ ⊤ → 11 ≤ K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGMathieuTwelveOuterBudgetOfFixedCapacity.proper_index_ge_eleven
      (K.map e.toMonoidHom) hmap
    have heindex : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rwa [heindex] at hi
  have hbase : B ^ 3 ≤ 5 ^ (11 + 1) :=
    (Nat.pow_le_pow_left hB 3).trans (by decide)
  have hsquare : 11 ^ 2 ≤ Nat.card E.Simple := by rw [hcardS]; decide
  rcases SmallFibreNonaffineClassPacketResidual.subnormal_gap_or_single_short_index
      π hπ c hc hsize E 11 (by decide) hindex hsquare hbase H hH with
      hgap | ⟨hk,K,hK,hdegree,_,_⟩
  · exact hgap
  · have hn : 11 ≤ Nat.card Y := by rw [hdegree]; exact hindex K hK
    have htop : ∀ L : Subgroup (Top (A := A) (X := Y)), L.IsSubnormal →
        Nat.card (ConjClasses L) ≤ 75 := by
      intro L hL
      have hh : Nat.card (ConjClasses L) ≤ B := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.subnormal_class_card_le_outer_wreath L hL
      exact hh.trans hB
    rcases hc with rfl | rfl
    · letI : Fintype Y := Fintype.ofFinite Y
      letI : DecidableEq Y := Classical.decEq Y
      have htopCard : Nat.card (Top (A := A) (X := Y)) ≤ 475200 := by
        calc
          _ ≤ Nat.card E.Simple * Nat.card (Outer E.Simple) := by
            simpa only [hk,pow_one,Nat.factorial_one,mul_one] using E.card_le_simple_outer_wreath
          _ ≤ 95040 * 5 := Nat.mul_le_mul hcardS.le houter
          _ = 475200 := by decide
      have hns : ∀ a : A, ¬(topMap (A := A) (X := Y) a).IsSwap := by
        intro a ha
        have ht : Top (A := A) (X := Y) = ⊤ :=
          SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
            (Top (A := A) (X := Y)) E hk (topMap (A := A) (X := Y) a) ha ⟨a,rfl⟩
        have hsym : Nat.card (Top (A := A) (X := Y)) = (Nat.card Y).factorial := by
          rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
        have hlarge : 475200 < (Nat.card Y).factorial :=
          (by decide : 475200 < (11 : ℕ).factorial).trans_le (Nat.factorial_le hn)
        rw [hsym] at htopCard
        omega
      have hbound := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
        π hπ (fun y => (hsize y).le) (by omega) 75 (by decide) htop hns H hH
      have hnum := SmallFibreSeventyFiveClassEnvelope.binary_unsigned_gap (Nat.card Y) hn
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
      have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
      simpa only [hcard,Nat.mul_comm (Nat.card Y) 2] using hh
    · have hlocal : ∀ y (L : Subgroup (Equiv.Perm (originalBlockFibre π y))),
          Nat.card (ConjClasses L) ≤ 3 :=
        fun y L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize y).le L
      have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
        π hπ 3 hlocal 75 htop H hH
      have hnum := SmallFibreSeventyFiveClassEnvelope.ternary_gap (Nat.card Y) hn
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
      have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
      simpa only [hcard,Nat.mul_comm (Nat.card Y) 3] using hh

theorem original_component_class_cube
    {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (E : NonaffineData D.Component D.Fibre) (e : E.Simple ≃* Model)
    (hdegree : 4 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ n : ℕ, n < Nat.card Ω → 4 ≤ n →
      ∀ L : Subgroup (Equiv.Perm (Fin n)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  by_cases hlarge : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hdegree hlarge D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
    have htwo := D.degrees_ge_two.2
    omega
  exact SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
    D.map D.map_equivariant D.base (Nat.card D.Fibre) hdegree rfl hsmall
    (fun L hL hne => proper_subnormal_class_cube_gap E e L hL hne) hSmaller

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCompleteClassConsumers
