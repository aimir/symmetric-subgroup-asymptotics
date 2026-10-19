import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import SymmetricSubgroupAsymptotics.OriginalKernelMonolithicSocleCoinvariance

/-! The literal A4 image forces its Klein subgroup to act trivially on
 the entire retained original translation section whenever the quotient
 socle has nonzero image. The original normal subgroup is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalSocleCoinvariance
open OriginalKernelModuleChart

abbrev Top := alternatingGroup (Fin 4)
abbrev klein : Subgroup Top := alternatingGroup.kleinFour (Fin 4)

theorem klein_le_nontrivial_normal (D : Subgroup Top)
    (hD : D.Normal) (hne : D ≠ ⊥) : klein ≤ D := by
  rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy D hD with h | h | h
  · exact (hne h).elim
  · rw [h]
  · rw [h]
    exact le_top

theorem dichotomy {G : Type} [Group G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) Top) (E : OriginalKernelModuleChart pi A)
    (N : Subgroup G) [N.Normal] :
    finiteGroupSocle (G ⧸ N) ≤ (base pi N).ker ∨
      klein ≤ ((E.sectionRepresentation pi A N).ρ.asGroupHom.comp
        (sectionTop pi N hpi)).ker :=
  E.retained_monolith_coinvariance pi A N hpi klein klein_le_nontrivial_normal

end SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalSocleCoinvariance
