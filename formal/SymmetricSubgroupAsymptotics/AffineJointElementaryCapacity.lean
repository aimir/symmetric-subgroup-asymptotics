import SymmetricSubgroupAsymptotics.AffineNormalGraphFibre
import SymmetricSubgroupAsymptotics.CocycleGeneratorBound

/-!
# Joint affine elementary capacity from invariant and normal-graph codes

This file isolates the finite counting step in the affine chief-layer
argument.  Normal intersections are first coded by their literal invariant
subrepresentation.  Inside one invariant intersection and one retained top,
the normal-section graph is charged once.  The section and first-cohomology
factors are then bounded with a generating tuple for the actual section top.

The normal-section graph is no longer an input.  It is supplied by
`affineNormalGraphFibre_card_le`, which reconstructs every literal normal
subgroup from its retained invariant intersection and one normal-complement
graph in the exact quotient section.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (pi : G →* B) (hpi : Function.Surjective pi)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart pi A)

/-- Data needed to turn the retained affine normal-axis coding into one
`ElementaryLayerJointCapacityBound`.  `H` counts invariant intersections;
`g` controls first cohomology; `v` is a faithful permutation degree for the
literal quotient group. -/
structure AffineJointElementaryCapacityInput where
  H : ℕ
  g : ℕ
  v : ℕ
  invariantCount : Nat.card (Subrepresentation A.ρ) ≤ Nat.card A ^ H
  sectionGenerators : ∀ N : {N : Subgroup G // N.Normal},
    ∃ generators : Fin g → G ⧸ (pi.ker ⊔ N.1),
      Subgroup.closure (Set.range generators) = ⊤
  /-- The sharp Schur capacity of every literal quotient section. -/
  sharpSectionCapacity : ∀ N : {N : Subgroup G // N.Normal},
    representationSchurCapacity
      (E.sectionRepresentation pi A N.1).ρ ≤ H
  /-- The original source sectional-rank bound, retained through every
  quotient stage. -/
  sectionalRank : PrimeSectionalRankBound p G (v / p)

namespace AffineJointElementaryCapacityInput

variable (D : AffineJointElementaryCapacityInput p pi A E)

private theorem section_card_le
    (N : {N : Subgroup G // N.Normal}) :
    Nat.card (E.sectionRepresentation pi A N.1) ≤ Nat.card A := by
  change Nat.card (A ⧸ E.normalSpace pi A N.1) ≤ Nat.card A
  exact Nat.card_le_card_of_surjective
    (E.normalSpace pi A N.1).mkQ
    (E.normalSpace pi A N.1).mkQ_surjective

private theorem axisCoefficient_le
    (N : {N : Subgroup G // N.Normal}) :
    elementaryLayerAxisCoefficient p pi A E N ≤
      (Nat.card A : ℝ) ^ (D.g + 1) := by
  obtain ⟨generators, hgenerators⟩ := D.sectionGenerators N
  let S := E.sectionRepresentation pi A N.1
  letI : Finite S := Finite.of_surjective
    (E.normalSpace pi A N.1).mkQ
    (E.normalSpace pi A N.1).mkQ_surjective
  have hS : Nat.card S ≤ Nat.card A := section_card_le p pi A E N
  have hH1 : Nat.card (groupCohomology.H1 S) ≤ Nat.card S ^ D.g :=
    firstCohomology_card_le_generator_power S D.g generators hgenerators
  unfold elementaryLayerAxisCoefficient
  calc
    (Nat.card S : ℝ) * Nat.card (groupCohomology.H1 S) ≤
        (Nat.card S : ℝ) * (Nat.card S : ℝ) ^ D.g := by
      gcongr
      exact_mod_cast hH1
    _ = (Nat.card S : ℝ) ^ (D.g + 1) := by
      rw [pow_succ']
    _ ≤ (Nat.card A : ℝ) ^ (D.g + 1) := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hS) _

private theorem fixedTop_card_le
    (top : {top : Subgroup B // top.Normal}) :
    Nat.card {N : {N : Subgroup G // N.Normal} //
      elementaryLayerTopAxis pi hpi N = top} ≤
      Nat.card A ^ D.H * p ^ (D.H * (D.v / p)) := by
  let X := {N : {N : Subgroup G // N.Normal} //
    elementaryLayerTopAxis pi hpi N = top}
  let f : X → Subrepresentation A.ρ := fun N ↦
    E.normalSubrepresentation pi hpi A N.1.1
  have hfibre : ∀ W : Subrepresentation A.ρ,
      Nat.card {N : X // f N = W} ≤ p ^ (D.H * (D.v / p)) := by
    intro W
    let j : {N : X // f N = W} →
        {N : {N : Subgroup G // N.Normal} //
          elementaryLayerTopAxis pi hpi N = top ∧
          E.normalSubrepresentation pi hpi A N.1 = W} :=
      fun N ↦ ⟨N.1.1, N.1.2, N.2⟩
    have hj : Function.Injective j := by
      intro N M h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z ↦ z.1) h
    exact (Nat.card_le_card_of_injective j hj).trans
      (affineNormalGraphFibre_card_le p pi hpi A E top W
        (D.v / p) D.H D.sectionalRank D.sharpSectionCapacity)
  calc
    Nat.card X ≤ Nat.card (Subrepresentation A.ρ) *
        p ^ (D.H * (D.v / p)) :=
      natCard_le_mul_of_fibre_le f _ hfibre
    _ ≤ Nat.card A ^ D.H * p ^ (D.H * (D.v / p)) :=
      Nat.mul_le_mul_right _
        D.invariantCount

/-- The explicit finite coefficient for one elementary affine layer. -/
def coefficient : ℝ :=
  (Nat.card A : ℝ) ^ D.H *
    (p : ℝ) ^ (D.H * (D.v / p)) *
    (Nat.card A : ℝ) ^ (D.g + 1)

theorem coefficient_nonneg :
    0 ≤ coefficient p pi A E D := by
  unfold coefficient
  positivity

/-- Assemble the exact joint elementary-layer bound.  The source exponent
uses the sharp Schur capacity `H` proved simultaneously for every literal
normal section.  The same `H` also pays for the invariant-intersection and
normal-graph incidence in the finite coefficient. -/
noncomputable def toJointCapacity :
    ElementaryLayerJointCapacityBound p pi hpi A E where
  capacity := D.H
  capacity_nonneg := by positivity
  section_capacity := by
    intro N
    exact D.sharpSectionCapacity N
  coefficient := coefficient p pi A E D
  coefficient_nonneg := coefficient_nonneg p pi A E D
  fixed_top_fibre := by
    intro top
    have hpoint : ∀ N : {N : {N : Subgroup G // N.Normal} //
        elementaryLayerTopAxis pi hpi N = top},
        elementaryLayerAxisCoefficient p pi A E N.1 ≤
          (Nat.card A : ℝ) ^ (D.g + 1) :=
      fun N ↦ axisCoefficient_le p pi A E D N.1
    have hsum := Finset.sum_le_card_nsmul
      (Finset.univ : Finset {N : {N : Subgroup G // N.Normal} //
        elementaryLayerTopAxis pi hpi N = top})
      (fun N : {N : {N : Subgroup G // N.Normal} //
        elementaryLayerTopAxis pi hpi N = top} ↦
          elementaryLayerAxisCoefficient p pi A E N.1)
      ((Nat.card A : ℝ) ^ (D.g + 1))
      (fun N _ ↦ hpoint N)
    calc
      (∑ N : {N : {N : Subgroup G // N.Normal} //
          elementaryLayerTopAxis pi hpi N = top},
          elementaryLayerAxisCoefficient p pi A E N.1) ≤
          (Nat.card {N : {N : Subgroup G // N.Normal} //
            elementaryLayerTopAxis pi hpi N = top} : ℝ) *
            (Nat.card A : ℝ) ^ (D.g + 1) := by
        simpa [nsmul_eq_mul, Nat.card_eq_fintype_card] using hsum
      _ ≤ ((Nat.card A : ℝ) ^ D.H *
          (p : ℝ) ^ (D.H * (D.v / p))) *
          (Nat.card A : ℝ) ^ (D.g + 1) := by
        gcongr
        exact_mod_cast fixedTop_card_le p pi hpi A E D top
      _ = coefficient p pi A E D := by rfl

end AffineJointElementaryCapacityInput
end SymmetricSubgroupAsymptotics

end
