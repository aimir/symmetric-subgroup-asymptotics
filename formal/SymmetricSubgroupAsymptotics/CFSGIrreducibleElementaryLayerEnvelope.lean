import SymmetricSubgroupAsymptotics.FixedTargetElementaryLayerEnvelope
import SymmetricSubgroupAsymptotics.CFSGSurjectiveRepresentationIrreducible
import SymmetricSubgroupAsymptotics.CFSGElementaryMinimalNormalIrreducible

/-! Every nonzero literal normal section of an irreducible elementary kernel
is irreducible for its actual descended top. Its Schur capacity is at most
one, including the zero section. The complete same-source envelope thus
pays one prime-log slope for the whole layer, rather than its dimension.
All original normal axes, extension maps and H1 constants are retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (π : G →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart π A)
include hπ

theorem irreducibleLayer_section_capacity_le_one
    (hirr : Representation.IsIrreducible A.ρ)
    (N : {N : Subgroup G // N.Normal}) :
    representationSchurCapacity (E.sectionRepresentation π A N.1).ρ ≤ 1 := by
  letI : Finite (E.sectionRepresentation π A N.1) :=
    Finite.of_surjective (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  by_cases hs : Subsingleton (E.sectionRepresentation π A N.1)
  · letI : Subsingleton (E.sectionRepresentation π A N.1) := hs
    have hd : Module.finrank (ZMod p) (E.sectionRepresentation π A N.1) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact (representationSchurCapacity_le_dimension _).trans (by rw [hd]; norm_num)
  · letI : Nontrivial (E.sectionRepresentation π A N.1) :=
      not_subsingleton_iff_nontrivial.mp hs
    apply representationSchurCapacity_le_one_of_irreducible
    exact representationIrreducible_of_surjective_equivariant
      A.ρ (E.sectionRepresentation π A N.1).ρ
      (OriginalKernelModuleChart.sectionLabelTop π N.1 hπ)
      (E.normalSpace π A N.1).mkQ (E.normalSpace π A N.1).mkQ_surjective
      (fun b v => E.sectionRepresentation_mkQ_sectionLabelTop π A N.1 hπ b v) hirr

theorem irreducibleLayer_axis_epi_le
    (hirr : Representation.IsIrreducible A.ρ)
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
      completeQuotientWeight (R := B) J *
        ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
          Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1)) *
          (p : ℝ) ^ ((1 : ℝ) * ((b : ℝ) / p))) := by
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
          (irreducibleLayer_section_capacity_le_one p π hπ A E hirr N) hb
    · positivity
  · positivity
  · exact completeQuotientWeight_nonneg J

/-- Complete fixed-source composition envelope across one elementary normal
layer.  Literal normal axes, quotient extensions, cohomology fibres, and the
same source `J` are all retained until the final finite sum. -/
theorem completeQuotientWeight_le_irreducibleLayer
    (hirr : Representation.IsIrreducible A.ρ)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      elementaryLayerEnvelopeConstant p π A E *
        (p : ℝ) ^ ((1 : ℝ) * ((b : ℝ) / p)) *
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
            (p : ℝ) ^ ((1 : ℝ) * ((b : ℝ) / p))) :=
      Finset.sum_le_sum (fun N _ =>
        irreducibleLayer_axis_epi_le p π hπ A E hirr N J)
    _ = elementaryLayerEnvelopeConstant p π A E *
        (p : ℝ) ^ ((1 : ℝ) * ((b : ℝ) / p)) *
        completeQuotientWeight (R := B) J := by
      unfold elementaryLayerEnvelopeConstant
      calc
        ∑ N : {N : Subgroup G // N.Normal},
            completeQuotientWeight (R := B) J *
              ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
                Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1)) *
                (p : ℝ) ^ ((1 : ℝ) * ((b : ℝ) / p))) =
          ∑ N : {N : Subgroup G // N.Normal},
            ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
              Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1))) *
              ((p : ℝ) ^ ((1 : ℝ) * ((b : ℝ) / p)) *
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
