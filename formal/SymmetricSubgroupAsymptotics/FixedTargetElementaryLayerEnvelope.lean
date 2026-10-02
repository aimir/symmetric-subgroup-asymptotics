import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre
import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-!
# A complete fixed-target envelope across one elementary normal layer

For a literal onto map `π : G ↠ B` whose kernel is given in elementary
`p`-module coordinates, every original normal quotient `G/N` is counted
through its exact descended kernel section.  The permutation-source rank
bound applies to the actual kernel of the same top epimorphism.  Summing only
after this retained-axis estimate gives one fixed target constant times
`p^(dim(A)b/p) Z_J(B)`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (π : G →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart π A)

/-- The fixed constant left after summing the exact section module and
cohomology factors over all literal normal axes. -/
def elementaryLayerEnvelopeConstant : ℝ :=
  letI : Fintype {N : Subgroup G // N.Normal} :=
    Subtype.fintype Subgroup.Normal
  ∑ N : {N : Subgroup G // N.Normal},
    (Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
      Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1))

theorem elementaryLayerEnvelopeConstant_nonneg :
    0 ≤ elementaryLayerEnvelopeConstant p π A E := by
  unfold elementaryLayerEnvelopeConstant
  positivity

include hπ

/-- The descended acting top on one literal normal axis is an actual quotient
of `B`, hence its epimorphism count is bounded by the complete quotient
weight of `B` on the same source. -/
theorem elementaryLayer_top_epi_le_completeQuotientWeight
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ (π.ker ⊔ N.1))) : ℝ) ≤
      completeQuotientWeight (R := B) J := by
  let K : Subgroup B := (π.ker ⊔ N.1).map π
  haveI hsup : (π.ker ⊔ N.1).Normal := inferInstance
  haveI hK : K.Normal := Subgroup.Normal.map hsup π hπ
  let e : (G ⧸ (π.ker ⊔ N.1)) ≃* (B ⧸ K) :=
    quotientEquivOfKerLe π hπ (π.ker ⊔ N.1) le_sup_left
  rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
  exact card_groupEpimorphism_le_completeQuotientWeight J
    ⟨K, inferInstance⟩ (MulEquiv.refl _)

/-- Every descended kernel section has Schur capacity at most the dimension
of the original elementary kernel module. -/
theorem elementaryLayer_section_capacity_le
    (N : {N : Subgroup G // N.Normal}) :
    representationSchurCapacity (E.sectionRepresentation π A N.1).ρ ≤
      Module.finrank (ZMod p) A := by
  letI : Finite (E.sectionRepresentation π A N.1) :=
    Finite.of_surjective (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  calc
    representationSchurCapacity (E.sectionRepresentation π A N.1).ρ ≤
        (Module.finrank (ZMod p)
          (E.sectionRepresentation π A N.1).ρ.asModule : ℝ) :=
      representationSchurCapacity_le_dimension _
    _ = (Module.finrank (ZMod p) (E.sectionModule π A N.1) : ℝ) := by
      exact_mod_cast
        (E.sectionRepresentation π A N.1).ρ.asModuleEquiv.finrank_eq
    _ ≤ (Module.finrank (ZMod p) A : ℝ) := by
      exact_mod_cast (E.normalSpace π A N.1).finrank_quotient_le

/-- One literal normal axis, with its exact descended extension and original
source, is controlled by the complete top weight and the uniform elementary
rank exponent. -/
theorem elementaryLayer_axis_epi_le
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
      completeQuotientWeight (R := B) J *
        ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
          Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1)) *
          (p : ℝ) ^ ((Module.finrank (ZMod p) A : ℝ) * ((b : ℝ) / p))) := by
  letI : Finite (E.sectionRepresentation π A N.1) :=
    Finite.of_surjective (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  have h := fusionEpimorphism_survival_card_le_schur_of_permutation_source
    p J (OriginalKernelModuleChart.base π N.1)
      (OriginalKernelModuleChart.base_surjective π N.1)
      (E.sectionRepresentation π A N.1) (E.quotientChart π A N.1)
      (fun _ => True)
  have hcard : Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // True} =
      Nat.card (GroupEpimorphism J (G ⧸ N.1)) := by simp
  rw [hcard] at h
  apply h.trans
  have htop := elementaryLayer_top_epi_le_completeQuotientWeight
    π hπ N J
  apply mul_le_mul htop
  · apply mul_le_mul_of_nonneg_left
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (Fact.out : p.Prime).one_lt.le
      · have hb : 0 ≤ (b : ℝ) / p := by positivity
        exact mul_le_mul_of_nonneg_right
          (elementaryLayer_section_capacity_le p π hπ A E N) hb
    · positivity
  · positivity
  · exact completeQuotientWeight_nonneg J

/-- Complete fixed-source composition envelope across one elementary normal
layer.  Literal normal axes, quotient extensions, cohomology fibres, and the
same source `J` are all retained until the final finite sum. -/
theorem completeQuotientWeight_le_elementaryLayer
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      elementaryLayerEnvelopeConstant p π A E *
        (p : ℝ) ^ ((Module.finrank (ZMod p) A : ℝ) * ((b : ℝ) / p)) *
        completeQuotientWeight (R := B) J := by
  letI : Fintype {N : Subgroup G // N.Normal} :=
    Subtype.fintype Subgroup.Normal
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ)) ≤
      ∑ N : {N : Subgroup G // N.Normal},
        completeQuotientWeight (R := B) J *
          ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
            Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1)) *
            (p : ℝ) ^ ((Module.finrank (ZMod p) A : ℝ) * ((b : ℝ) / p))) :=
      Finset.sum_le_sum (fun N _ =>
        elementaryLayer_axis_epi_le p π hπ A E N J)
    _ = elementaryLayerEnvelopeConstant p π A E *
        (p : ℝ) ^ ((Module.finrank (ZMod p) A : ℝ) * ((b : ℝ) / p)) *
        completeQuotientWeight (R := B) J := by
      unfold elementaryLayerEnvelopeConstant
      calc
        ∑ N : {N : Subgroup G // N.Normal},
            completeQuotientWeight (R := B) J *
              ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
                Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1)) *
                (p : ℝ) ^ ((Module.finrank (ZMod p) A : ℝ) * ((b : ℝ) / p))) =
          ∑ N : {N : Subgroup G // N.Normal},
            ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
              Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1))) *
              ((p : ℝ) ^ ((Module.finrank (ZMod p) A : ℝ) * ((b : ℝ) / p)) *
                completeQuotientWeight (R := B) J) := by
            apply Finset.sum_congr rfl
            intro N _
            ring
        _ = _ := by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro N _
          ring

end SymmetricSubgroupAsymptotics

end
