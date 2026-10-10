import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightProducerInterfaces
import SymmetricSubgroupAsymptotics.SimpleChiefFamilies
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.GroupTheory.Perm.Fin

/-!
# Structural packages for the natural paired-eight tops

The final paired-eight rows are the literal natural actions of `A_8` and
`S_8`.  Their retained two-generator tuples remain available to the small
module and coupled-head emitters, but their quotient socles are handled by
the two- and three-state normal lattices.  No Cayley table for either large
group is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightStructuralTops

namespace Shared := DegreeTwoPairedEightSharedTops
namespace Producers := PrimitiveAffineDegreeTwoPairedEightProducerInterfaces

/-! ## Stable selected-top APIs -/

namespace Row23

abbrev Source := Shared.Top23

def group : Group Source := inferInstance

def generators := Producers.Row23.generators

abbrev Top : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range generators)

def originalEquiv : Source ≃* Top := MulEquiv.refl Source

def ambient (i : Fin 2) : Source :=
  ⟨generators i, Subgroup.subset_closure (Set.mem_range_self i)⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ := by
  apply top_unique
  intro x _hx
  induction x.property using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨i, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => exact Subgroup.inv_mem _ hx

end Row23

namespace Row24

abbrev Source := Shared.Top24

def group : Group Source := inferInstance

def generators := Producers.Row24.generators

abbrev Top : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range generators)

def originalEquiv : Source ≃* Top := MulEquiv.refl Source

def ambient (i : Fin 2) : Source :=
  ⟨generators i, Subgroup.subset_closure (Set.mem_range_self i)⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ := by
  apply top_unique
  intro x _hx
  induction x.property using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨i, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => exact Subgroup.inv_mem _ hx

end Row24

/-! ## Structural quotient-socle families -/

/-- Every quotient of a simple group has a padded two-place socle
generator. -/
private noncomputable def simpleTopSocle
    (G : Type) [Group G] [IsSimpleGroup G] :
    ∀ N : {N : Subgroup G // N.Normal},
      SocleNormalGeneratorBound (G ⧸ N.1) 2 := by
  intro N
  rcases N.2.eq_bot_or_eq_top with hbot | htop
  · let e : G ⧸ N.1 ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans
        QuotientGroup.quotientBot
    letI : IsSimpleGroup (G ⧸ N.1) := e.isSimpleGroup
    exact (socleNormalGeneratorBound_one_of_isSimpleGroup _).mono
      (by norm_num)
  · letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
      QuotientGroup.subsingleton_quotient_top
    letI : Subsingleton (G ⧸ N.1) :=
      (QuotientGroup.quotientMulEquivOfEq htop).toEquiv.subsingleton
    exact (socleNormalGeneratorBound_one_of_subsingleton _).mono
      (by norm_num)

/-- Structural quotient-socle theorem for the natural `A_8` row. -/
noncomputable def row23TopSocle :
    ∀ N : {N : Subgroup Shared.Top23 // N.Normal},
      SocleNormalGeneratorBound (Shared.Top23 ⧸ N.1) 2 := by
  letI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let e : Shared.Top23 ≃* alternatingGroup (Fin 8) :=
    MulEquiv.subgroupCongr Shared.top23_eq_alternating
  letI : IsSimpleGroup Shared.Top23 := e.isSimpleGroup
  exact simpleTopSocle Shared.Top23

/-- The literal chain `1 < A_8 < S_8`, used after transporting the retained
row-24 subgroup to the full symmetric group. -/
private noncomputable def symmetricPermNormalChain :
    FiniteThreeNormalChainData (Equiv.Perm (Fin 8)) := by
  letI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let cycle : Equiv.Perm (Fin 8) := Fin.cycleRange 2
  have hcycle : Equiv.Perm.IsThreeCycle cycle :=
    Fin.isThreeCycle_cycleRange_two
  refine
    { middle := alternatingGroup (Fin 8)
      middle_normal := inferInstance
      middle_ne_bot :=
        (Subgroup.isSimpleGroup_iff.mp
          (show IsSimpleGroup (alternatingGroup (Fin 8)) from
            inferInstance)).1
      middle_ne_top := ?_
      normal_eq_bot_or_middle_or_top := ?_
      generator := cycle
      generator_mem := hcycle.mem_alternatingGroup
      generator_ne_one := hcycle.ne_one }
  · intro htop
    have hindex := alternatingGroup.index_eq_two (α := Fin 8)
    rw [htop, Subgroup.index_top] at hindex
    omega
  · intro N hN
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · right
      letI : N.Normal := hN
      haveI : Nontrivial N := Subgroup.nontrivial_iff_ne_bot.mpr hbot
      exact indexTwo_maximal (alternatingGroup (Fin 8))
        alternatingGroup.index_eq_two N
        (Equiv.Perm.alternatingGroup_le_of_normal
          (by norm_num) inferInstance)

/-- Structural quotient-socle theorem for the natural `S_8` row. -/
noncomputable def row24TopSocle :
    ∀ N : {N : Subgroup Shared.Top24 // N.Normal},
      SocleNormalGeneratorBound (Shared.Top24 ⧸ N.1) 2 :=
  let e : Shared.Top24 ≃* Equiv.Perm (Fin 8) :=
    (MulEquiv.subgroupCongr Shared.top24_eq_top).trans Subgroup.topEquiv
  (symmetricPermNormalChain.mapEquiv e.symm).
    quotientSocleGeneratorBound_two

end PrimitiveAffineDegreeTwoPairedEightStructuralTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
