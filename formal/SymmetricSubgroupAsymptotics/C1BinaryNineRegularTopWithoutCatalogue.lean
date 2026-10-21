import SymmetricSubgroupAsymptotics.C1BinaryNineRegularTop
import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudgetWithoutCatalogue

/-! Preserve the complete original-normal mixed binary-nine physical row;
only its exact source rank-budget producer is replaced by a proved theorem. -/
set_option autoImplicit false
noncomputable section
attribute [-instance] SymmetricSubgroupAsymptotics.originalNormalFintype
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- The binary-nine physical row with a constant independent of the source
degree.  The source pattern is required only on complete sources whose
surviving onto maps are accepted by the local predicate. -/
theorem C1BinaryNineTopOwnerWitness.physical_owner_bound_ternaryTop_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (U : Subgroup (Equiv.Perm (Fin 12)))
    (W : C1BinaryNineTopOwnerWitness U (Fin 12))
    (hregular : ∀ N : {N : Subgroup U // N.Normal},
      ∃ F : (W.originalKernelChart.sectionRepresentation
          W.projection W.baseRepresentation N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod 2)
          (U ⧸ (W.projection.ker ⊔ N.1))), Function.Injective F) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (∀ (N : {N : Subgroup U // N.Normal})
        (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
        P (fusionFullGoursatEncode N J β).1 → C1DegreeNineSourcePattern J) →
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 12) ≤
        c1EarlierKernel b .degreeTwelveMixed D
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  letI := W.label_finite
  obtain ⟨C, hC, hEpi⟩ := degreeNine_rankBudget_quotientEpimorphism_le_binary
    W.labelImage W.label_card W.labelImage_isPGroup
  refine ⟨∑ N : {N : Subgroup U // N.Normal},
      (originalNormalRegularConstant 2 W.projection W.baseRepresentation
        W.originalKernelChart N : ℝ) * C,
    Finset.sum_nonneg (fun N _ => mul_nonneg (Nat.cast_nonneg _) hC), ?_⟩
  intro b P hP hSource
  letI : Finite ↥W.baseRepresentation := by
    change Finite W.BaseVector
    infer_instance
  apply c1EarlierPhysical_regular_owner_bound_of_source (p := 2)
    .degreeTwelveMixed U W.projection W.baseRepresentation W.originalKernelChart
    hregular b P hP C1DegreeNineSourcePattern hSource (fun _ => C) (fun _ => hC)
  intro J hJ N
  letI : N.1.Normal := N.2
  have hbudget := hJ.rankBudget_without_catalogue hChief hgen hindex published8 h18 J
  have htop : (Nat.card (GroupEpimorphism J (U ⧸ (W.projection.ker ⊔ N.1))) : ℝ) ≤
      C * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) :=
    hEpi (W.labelAxisTop N.1) (W.labelAxisTop_surjective N.1) b J hbudget
  have hmass : (regularTopCharacterMass 2 J (U ⧸ (W.projection.ker ⊔ N.1)) : ℝ) ≤
      (Nat.card (GroupEpimorphism J (U ⧸ (W.projection.ker ⊔ N.1))) : ℝ) *
        (2 : ℝ) ^ (b / 2) := by
    exact_mod_cast regularTopCharacterMass_le_of_rank 2 (J := J)
      (B := U ⧸ (W.projection.ker ⊔ N.1)) (b / 2) (fun β => by
        have h := epimorphismKernel_binaryCharacterRank_le_half J β.1
        simpa only [Nat.card_fin] using h)
  calc
    (regularTopCharacterMass 2 J (U ⧸ (W.projection.ker ⊔ N.1)) : ℝ) ≤
        (Nat.card (GroupEpimorphism J (U ⧸ (W.projection.ker ⊔ N.1))) : ℝ) *
          (2 : ℝ) ^ (b / 2) := hmass
    _ ≤ (C * (2 : ℝ) ^ (((8 : ℝ) / 9) * b)) * (2 : ℝ) ^ (((1 : ℝ) / 2) * b) :=
      mul_le_mul htop (binaryKernelPower_le_half b) (by positivity)
        (mul_nonneg hC (by positivity))
    _ = C * (2 : ℝ) ^ (((25 : ℝ) / 18) * b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ C * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent .degreeTwelveMixed * b) := by
      simp only [c1EarlierExponent]
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (((25 : ℝ) / 18) * b) := by positivity
      nlinarith [mul_nonneg hC hp, (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

end SymmetricSubgroupAsymptotics
