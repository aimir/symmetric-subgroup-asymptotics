import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import SymmetricSubgroupAsymptotics.BinaryEightSeed15Transitivity
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8LargerBinarySeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed15Root1BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root2BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root3BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root4BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root5BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root6BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root7BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root8BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root9BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root10BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root11BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root12BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root13BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root14BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root15BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root16BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root17BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root18BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root19BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root20BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root21BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root22BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root23BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root24BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root25BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root26BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root27BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root28BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root29BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root30BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root31BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root32BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root33BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root34BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root35BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root36BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root37BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root38BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root39BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root40BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root41BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root42BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed15Root43BinaryExtension

/-! Actual overgroups above original8T15. Every proper adjunction has an
ordinary-word certified larger binary subgroup. That subgroup retains its
actual original-point action throughout transport and registry dispatch. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed15OvergroupCoverage
open S8Seed15LeftCosets

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 32 W

def EqSeedOrEscape (W : Subgroup Ambient) : Prop := W = H ∨ Escape W

theorem escape_of_extension (P W : Subgroup Ambient) (hPW : P ≤ W)
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hcard : 32 < Nat.card P) : Escape W :=
  ⟨P, hPW, hP,
    permutationSubgroupTransitive_mono H P hHP BinaryEightSeed15Transitivity.transitive,
    hcard⟩

theorem root_property (k : Fin 44) : EqSeedOrEscape
    (H ⊔ Subgroup.closure {representatives (S8Seed15NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl S8Seed15NormalizerRoots.root_zero_eq_seed
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root1BinaryExtension.extended_le_adjoin
      S8Seed15Root1BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root1BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root2BinaryExtension.extended_le_adjoin
      S8Seed15Root2BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root2BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root3BinaryExtension.extended_le_adjoin
      S8Seed15Root3BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root3BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root4BinaryExtension.extended_le_adjoin
      S8Seed15Root4BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root4BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root5BinaryExtension.extended_le_adjoin
      S8Seed15Root5BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root5BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root6BinaryExtension.extended_le_adjoin
      S8Seed15Root6BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root6BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root7BinaryExtension.extended_le_adjoin
      S8Seed15Root7BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root7BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root8BinaryExtension.extended_le_adjoin
      S8Seed15Root8BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root8BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root9BinaryExtension.extended_le_adjoin
      S8Seed15Root9BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root9BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root10BinaryExtension.extended_le_adjoin
      S8Seed15Root10BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root10BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root11BinaryExtension.extended_le_adjoin
      S8Seed15Root11BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root11BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root12BinaryExtension.extended_le_adjoin
      S8Seed15Root12BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root12BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root13BinaryExtension.extended_le_adjoin
      S8Seed15Root13BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root13BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root14BinaryExtension.extended_le_adjoin
      S8Seed15Root14BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root14BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root15BinaryExtension.extended_le_adjoin
      S8Seed15Root15BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root15BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root16BinaryExtension.extended_le_adjoin
      S8Seed15Root16BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root16BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root17BinaryExtension.extended_le_adjoin
      S8Seed15Root17BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root17BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root18BinaryExtension.extended_le_adjoin
      S8Seed15Root18BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root18BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root19BinaryExtension.extended_le_adjoin
      S8Seed15Root19BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root19BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root20BinaryExtension.extended_le_adjoin
      S8Seed15Root20BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root20BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root21BinaryExtension.extended_le_adjoin
      S8Seed15Root21BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root21BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root22BinaryExtension.extended_le_adjoin
      S8Seed15Root22BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root22BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root23BinaryExtension.extended_le_adjoin
      S8Seed15Root23BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root23BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root24BinaryExtension.extended_le_adjoin
      S8Seed15Root24BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root24BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root25BinaryExtension.extended_le_adjoin
      S8Seed15Root25BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root25BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root26BinaryExtension.extended_le_adjoin
      S8Seed15Root26BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root26BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root27BinaryExtension.extended_le_adjoin
      S8Seed15Root27BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root27BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root28BinaryExtension.extended_le_adjoin
      S8Seed15Root28BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root28BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root29BinaryExtension.extended_le_adjoin
      S8Seed15Root29BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root29BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root30BinaryExtension.extended_le_adjoin
      S8Seed15Root30BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root30BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root31BinaryExtension.extended_le_adjoin
      S8Seed15Root31BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root31BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root32BinaryExtension.extended_le_adjoin
      S8Seed15Root32BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root32BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root33BinaryExtension.extended_le_adjoin
      S8Seed15Root33BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root33BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root34BinaryExtension.extended_le_adjoin
      S8Seed15Root34BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root34BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root35BinaryExtension.extended_le_adjoin
      S8Seed15Root35BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root35BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root36BinaryExtension.extended_le_adjoin
      S8Seed15Root36BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root36BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root37BinaryExtension.extended_le_adjoin
      S8Seed15Root37BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root37BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root38BinaryExtension.extended_le_adjoin
      S8Seed15Root38BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root38BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root39BinaryExtension.extended_le_adjoin
      S8Seed15Root39BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root39BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root40BinaryExtension.extended_le_adjoin
      S8Seed15Root40BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root40BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root41BinaryExtension.extended_le_adjoin
      S8Seed15Root41BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root41BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root42BinaryExtension.extended_le_adjoin
      S8Seed15Root42BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root42BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed15Root43BinaryExtension.extended_le_adjoin
      S8Seed15Root43BinaryExtension.extended_isPGroup le_sup_left S8Seed15Root43BinaryExtension.extended_card_gt)

theorem property_conjugate (c : Ambient) (hc : MulAut.conj c • H = H)
    (W : Subgroup Ambient) (hW : EqSeedOrEscape W) :
    EqSeedOrEscape (MulAut.conj c • W) := by
  rcases hW with rfl | hescape
  · exact Or.inl hc
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate 2 32 c W hescape)

theorem adjoin_property (g : Ambient) : EqSeedOrEscape (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed15LeftCosets.certificate.covers
    SymmetricEightTwoGenerators.generators_full g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed15NormalizerRoots.reduction.property_representative
    EqSeedOrEscape property_conjugate root_property i
  rw [← he] at hp
  exact hp

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) : U = H ∨ Escape U := by
  classical
  by_cases heq : U = H
  · exact Or.inl heq
  · right
    have hnot : ¬ U ≤ H := fun h => heq (le_antisymm h hHU)
    obtain ⟨g, hgU, hgH⟩ := Set.not_subset.mp hnot
    rcases adjoin_property g with heq | hescape
    · have hg : g ∈ H ⊔ Subgroup.closure {g} :=
        (show Subgroup.closure {g} ≤ H ⊔ Subgroup.closure {g} from le_sup_right)
          (Subgroup.subset_closure (by simp))
      exact False.elim (hgH (heq ▸ hg))
    · apply PermutationPrimePowerSeedEscape.mono 2 32 _ U _ hescape
      refine sup_le hHU ((Subgroup.closure_le U).mpr ?_)
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hgU

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) : U = Q ∨ Escape U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with heq | hescape
  · left
    have hsame : MulAut.conj c • U = MulAut.conj c • Q := heq.trans hc.symm
    have h := congrArg (fun W : Subgroup Ambient => MulAut.conj c⁻¹ • W) hsame
    simpa only [map_inv, inv_smul_smul] using h
  · right
    have h := PermutationPrimePowerSeedEscape.conjugate 2 32 c⁻¹ _ hescape
    simpa only [map_inv, inv_smul_smul] using h

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 5) BinaryMenuCayley8T15.exact_card

theorem canonical_complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases complete_of_conjugate U Q hQU c hc with heq | ⟨P, hPU, hp, ht, hcard⟩
  · have hp : IsPGroup 2 U := by
      rw [heq]
      exact S8CanonicalNonbinaryTransport.isPGroup_of_conjugate Q H c hc seed_isPGroup
    exact False.elim (hnot hp)
  · exact S8LargerBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed15OvergroupCoverage
end
