import SymmetricSubgroupAsymptotics.OriginalKernelSectionGeneration
import SymmetricSubgroupAsymptotics.RepresentationFiniteImageDimension
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-! A small residual top bounds the order of the actual original quotient.
The kernel is the section by the original normal denominator, even when
that denominator is not contained in the elementary kernel. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
open Non2UnipotentPrefixFiniteMenu

variable {G B : Type} [Group G] [Finite G] [Group B]
  (pi : G →* B) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) B) [Finite A]
  (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

include hpi in
/-- The residual acting top is exactly the quotient by the image of the
original normal denominator. This identifies cardinalities without replacing
the original quotient whose source will be counted. -/
theorem residualTop_card_eq :
    Nat.card (G ⧸ (pi.ker ⊔ N)) = Nat.card (B ⧸ N.map pi) := by
  letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
  have hker : pi.ker.map pi = ⊥ :=
    (Subgroup.map_eq_bot_iff (H := pi.ker)).mpr le_rfl
  have hmap : (pi.ker ⊔ N).map pi = N.map pi := by
    rw [Subgroup.map_sup, hker, bot_sup_eq]
  letI : ((pi.ker ⊔ N).map pi).Normal :=
    (inferInstance : (pi.ker ⊔ N).Normal).map pi hpi
  let e := quotientEquivOfKerLe pi hpi (pi.ker ⊔ N) le_sup_left
  have he := Nat.card_congr e.toEquiv
  simpa only [hmap] using he

include E hpi in
/-- No split extension or restriction `N ≤ ker pi` is used. A cyclic
original kernel row descends to the same physical quotient and an actual
top of order at most two, so that quotient has order at most eight. -/
theorem quotient_card_le_eight_of_cyclic_small_top
    (hgen : RepresentationGeneratedBy A.ρ 1)
    (hsmall : Nat.card (G ⧸ (pi.ker ⊔ N)) ≤ 2) :
    Nat.card (G ⧸ N) ≤ 8 := by
  letI : Finite (E.sectionModule pi A N) :=
    Finite.of_surjective (E.sectionProjection pi A N)
      (E.sectionProjection_surjective pi A N)
  let sigma : Representation (ZMod 2) (G ⧸ (pi.ker ⊔ N))
      (E.sectionModule pi A N) := (E.sectionRepresentation pi A N).ρ
  exact ElementaryBinaryKernel.card_le_eight_of_cyclic_small_top
    sigma
    (QuotientGroup.mk' (pi.ker ⊔ N))
    (E.sectionGeneratedBy pi A N hpi hgen) hsmall
    (base pi N) (base_surjective pi N) (E.kernelEquiv pi A N).symm

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
