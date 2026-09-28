import SymmetricSubgroupAsymptotics.TernaryThreeBlockKernelChart
import SymmetricSubgroupAsymptotics.PermutationPGroupSection
import SymmetricSubgroupAsymptotics.BinaryPairResidualTop
import SymmetricSubgroupAsymptotics.FusionEpimorphismLifts

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

/-- One exact layer of the quotient-epimorphism induction.  The top maps
remain maps from the same complete source to the literal descended block
top.  The target-local module and cohomology factors are retained, while
the only source-dependent lift cost is the sharp `s b / 9` exponent, where
`s` is the number of blocks. -/
theorem quotient_epimorphism_card_le_top_mul_schur
    [Nontrivial D.Points] {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
      Nat.card (GroupEpimorphism J (U ⧸ (D.TopKernel ⊔ N))) *
        (Nat.card (D.sectionModule hU N) *
          Nat.card (groupCohomology.H1 (D.sectionRepresentation hU N)) *
          (3 : ℝ) ^ (((Nat.card D.Points : ℝ) / 3) * ((b : ℝ) / 3))) := by
  letI : Finite (D.sectionRepresentation hU N) :=
    Finite.of_surjective
      ((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
        (D.kernelModule hU) N).mkQ
      ((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
        (D.kernelModule hU) N).mkQ_surjective
  let P : ∀ beta : GroupEpimorphism J (U ⧸ (D.TopKernel ⊔ N)),
      Sylow 3 beta.1.ker := fun _ => Classical.choice inferInstance
  have hrank : ∀ beta : GroupEpimorphism J (U ⧸ (D.TopKernel ⊔ N)),
      (Module.finrank (ZMod 3)
        (PrimeAbelianization 3 (P beta : Subgroup beta.1.ker)) : ℝ) ≤
          (b : ℝ) / 3 := by
    intro beta
    exact permutationThreeGroup_sylowKernel_primeAbelianizationRank_le
      J beta.1 (P beta)
  have hschur := fusionEpimorphism_survival_card_le_schur_of_rank_bound
    3 (D.sectionBase N) (OriginalKernelModuleChart.base_surjective
      D.topMap.rangeRestrict N)
    (D.sectionRepresentation hU N) (D.sectionChart hU N) P
    (fun _ => True) (b : ℝ) hrank
  have hcapacity : representationSchurCapacity
      (D.sectionRepresentation hU N).ρ ≤ (Nat.card D.Points : ℝ) / 3 := by
    rw [pGroup_representationSchurCapacity
      (hU.to_quotient (D.TopKernel ⊔ N))]
    have hdim : (Module.finrank (ZMod 3)
        (D.sectionRepresentation hU N).ρ.invariants : ℝ) ≤
          ((Nat.card D.Points / 3 : ℕ) : ℝ) := by
      exact_mod_cast D.section_invariants_finrank_le_div hU N
    have hmul : 3 * (Nat.card D.Points / 3) ≤ Nat.card D.Points := by
      simpa only [mul_comm] using Nat.div_mul_le_self (Nat.card D.Points) 3
    have hmulR : (3 : ℝ) * ((Nat.card D.Points / 3 : ℕ) : ℝ) ≤
        (Nat.card D.Points : ℝ) := by exact_mod_cast hmul
    linarith
  have hpow :
      (3 : ℝ) ^ (representationSchurCapacity
          (D.sectionRepresentation hU N).ρ * ((b : ℝ) / 3)) ≤
        (3 : ℝ) ^ (((Nat.card D.Points : ℝ) / 3) * ((b : ℝ) / 3)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hcapacity (by positivity)
  calc
    (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) =
        Nat.card {f : GroupEpimorphism J (U ⧸ N) // True} := by simp
    _ ≤ Nat.card (GroupEpimorphism J (U ⧸ (D.TopKernel ⊔ N))) *
        (Nat.card (D.sectionModule hU N) *
          Nat.card (groupCohomology.H1 (D.sectionRepresentation hU N)) *
          (3 : ℝ) ^ (representationSchurCapacity
            (D.sectionRepresentation hU N).ρ * ((b : ℝ) / 3))) := hschur
    _ ≤ _ := by
      gcongr

end TransitiveThreeBlockCover
end SymmetricSubgroupAsymptotics

end
