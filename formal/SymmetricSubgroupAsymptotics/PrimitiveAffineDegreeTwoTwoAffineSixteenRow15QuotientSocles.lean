import SymmetricSubgroupAsymptotics.AffineWreathSimpleComplementNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow15WreathTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Every quotient of the original row15 top has cyclic socle as a normal
subgroup. Padding supplies the retained two-position registry interface. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow15QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PrimitiveAffineDegreeTwoTwoAffineSixteenRow15WreathTop

theorem linear_center_eq_bot : Subgroup.center R = ⊥ := by
  letI : IsSimpleGroup R := Row20.linearGroup_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R)
      (inferInstance : (Subgroup.center R).Normal) with h | h
  · exact h
  exfalso
  let s : R := ⟨singer, Row20.singer_mem⟩
  let b : R := ⟨swap, Row20.swap_mem⟩
  have hs : s ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top _
  have heq : swap * singer = singer * swap :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hs b)
  have hne : swap * singer ≠ singer * swap := by
    intro he
    have hv := congrArg (fun f : LinearGroup ↦ f firstVector) he
    have hmove : (swap * singer) firstVector ≠ (singer * swap) firstVector := by
      decide +kernel
    exact hmove hv
  exact hne heq

theorem model_normal_generators :
    ∀ N : Subgroup Model, N.Normal →
      ∃ x : Fin 1 → Model, Subgroup.normalClosure (Set.range x) = N := by
  letI : IsSimpleGroup R := Row20.linearGroup_isSimpleGroup
  exact AffineModel.wreath_normal_generating_singletons R Row20.irreducible
    linear_center_eq_bot firstVector firstVector_ne_zero

theorem top_normal_generators (N : Subgroup Top) (hN : N.Normal) :
    ∃ x : Fin 1 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective modelEquiv.toMonoidHom modelEquiv.surjective
    model_normal_generators N hN

theorem quotientSocle_one (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact (quotientSocle_one N.1).mono (by decide)

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row15.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row15.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow15QuotientSocles
end SymmetricSubgroupAsymptotics

end
