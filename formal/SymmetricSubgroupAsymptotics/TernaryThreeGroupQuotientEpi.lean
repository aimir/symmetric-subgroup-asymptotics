import SymmetricSubgroupAsymptotics.TernaryThreeBlockKernelChart
import SymmetricSubgroupAsymptotics.PermutationPGroupSection
import SymmetricSubgroupAsymptotics.BinaryPairResidualTop

/-!
# Arbitrary-normal ternary block-kernel sections

The concrete ternary block-kernel chart descends along every original
normal subgroup.  The actual faithful block top maps onto the descended
section top, and the literal quotient of the correlated coordinate module
is an equivariant permutation section.  Its whole invariant space therefore
has dimension at most one third of the number of blocks.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TransitiveThreeBlockCover

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x)

variable (hU : IsPGroup 3 U) (N : Subgroup U) [N.Normal]

/-- The exact quotient of the correlated block-kernel module by the
intersection with an arbitrary original normal subgroup. -/
abbrev sectionModule :=
  (D.originalKernelChart hU).sectionModule D.topMap.rangeRestrict (D.kernelModule hU) N

/-- The descended action of the literal original quotient top. -/
abbrev sectionRepresentation :
    Rep (ZMod 3) (U ⧸ (D.TopKernel ⊔ N)) :=
  (D.originalKernelChart hU).sectionRepresentation
    D.topMap.rangeRestrict (D.kernelModule hU) N

/-- The actual quotient `U/N` maps onto its exact block-kernel section top. -/
abbrev sectionBase : (U ⧸ N) →* U ⧸ (D.TopKernel ⊔ N) :=
  OriginalKernelModuleChart.base D.topMap.rangeRestrict N

/-- The arbitrary-normal quotient retains an exact original-kernel chart. -/
def sectionChart :
    OriginalKernelModuleChart (D.sectionBase N) (D.sectionRepresentation hU N) :=
  (D.originalKernelChart hU).quotientChart
    D.topMap.rangeRestrict (D.kernelModule hU) N

/-- The faithful block top maps onto the descended section top. -/
def sectionTopQuotient : D.Top →* U ⧸ (D.TopKernel ⊔ N) :=
  D.topMap.rangeRestrict.liftOfSurjective
    D.topMap.rangeRestrict_surjective
    ⟨QuotientGroup.mk' (D.TopKernel ⊔ N), by
      rw [QuotientGroup.ker_mk']
      exact le_sup_left⟩

@[simp] theorem sectionTopQuotient_apply (u : U) :
    D.sectionTopQuotient N (D.topMap.rangeRestrict u) =
      QuotientGroup.mk' (D.TopKernel ⊔ N) u :=
  MonoidHom.liftOfRightInverse_comp_apply D.topMap.rangeRestrict
    (Function.surjInv D.topMap.rangeRestrict_surjective)
    (Function.rightInverse_surjInv D.topMap.rangeRestrict_surjective) _ u

theorem sectionTopQuotient_surjective :
    Function.Surjective (D.sectionTopQuotient N) := by
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (D.TopKernel ⊔ N) q
  exact ⟨D.topMap.rangeRestrict u, D.sectionTopQuotient_apply N u⟩

/-- The quotient map from the correlated coordinate image to the exact
kernel section, viewed over the faithful block top. -/
def sectionTopIntertwiner :
    (D.kernelSubrepresentation hU).toRepresentation.IntertwiningMap
      ((D.sectionRepresentation hU N).ρ.comp (D.sectionTopQuotient N)) where
  toLinearMap := ((D.originalKernelChart hU).normalSpace
    D.topMap.rangeRestrict (D.kernelModule hU) N).mkQ
  isIntertwining' t := by
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := D.topMap.rangeRestrict_surjective t
    obtain ⟨k, hk⟩ := (D.kernelSpaceHom_bijective hU).2
      (Multiplicative.ofAdd v)
    have hv : (D.kernelSpaceHom hU k).toAdd = v :=
      congrArg Multiplicative.toAdd hk
    rw [← hv]
    have hcoords := D.kernelSubrepresentation_apply hU u k
    change ((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
        (D.kernelModule hU) N).mkQ
          ((D.kernelSubrepresentation hU).toRepresentation
            (D.topMap.rangeRestrict u) (D.kernelSpaceHom hU k).toAdd) =
      (D.sectionRepresentation hU N).ρ
        (D.sectionTopQuotient N (D.topMap.rangeRestrict u))
          (((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
            (D.kernelModule hU) N).mkQ (D.kernelSpaceHom hU k).toAdd)
    rw [hcoords, D.sectionTopQuotient_apply]
    exact ((D.originalKernelChart hU).sectionRepresentation_apply
      D.topMap.rangeRestrict (D.kernelModule hU) N u k).symm

/-- Every arbitrary-normal section of a non-base ternary block kernel has
at most one invariant coordinate per three blocks. -/
theorem section_invariants_finrank_le_div [Nontrivial D.Points] :
    Module.finrank (ZMod 3) (D.sectionRepresentation hU N).ρ.invariants ≤
      Nat.card D.Points / 3 := by
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  have h := pGroup_permutationSection_invariants_finrank_le_div
    (D.top_isPGroup hU)
    ((D.sectionRepresentation hU N).ρ.comp (D.sectionTopQuotient N))
    (D.kernelSubrepresentation hU) (D.sectionTopIntertwiner hU N)
    ((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
      (D.kernelModule hU) N).mkQ_surjective
  rw [representation_invariants_comp_onto
    (D.sectionRepresentation hU N).ρ (D.sectionTopQuotient N)
    (D.sectionTopQuotient_surjective N)] at h
  exact h

end TransitiveThreeBlockCover
end SymmetricSubgroupAsymptotics

end
