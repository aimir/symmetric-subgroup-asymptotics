import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleRootRanges
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSignedCommutation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGRankOneNoncommutation

/-! Cross-sign commutation distinguishes the two original simple
labels in every characteristic. Equal labels have a literal rank-one
Weyl noncommutation witness, separated by the actual opposed Sylows. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalRankOneWitness
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGGTwoD4GeckSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalOppositeAlignment
open CFSGGTwoD4GeckSimpleRootRanges CFSGTrialityGeckOvergroupWeylExtraction
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityGeckFixedRootWords
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] [Finite K]

private theorem opposite_simple_commute (i j : Fin 4) (hne : i ≠ j) (a b : K) :
    Commute (canonicalRoot rawData K false i a) (canonicalRoot rawData K true j b) :=
  CFSGSerreQuadraticSignedCommutation.roots_commute rawData K false true i j
    (by
      change ⁅fieldRoot (CFSGNormTwoGeckIntegralRealization.realizationData
          (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index) ℚ false i,
        fieldRoot (CFSGNormTwoGeckIntegralRealization.realizationData
          (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index) ℚ true j⁆ = 0
      rw [rational_E_eq, rational_F_eq, EF, if_neg hne]) a b

theorem original_distinct_opposite_commute [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.G₂ K)]
    (a b : Bool) (hne : a ≠ b) (x y : Multiplicative K) :
    Commute (originalSimpleHom K false a x) (originalSimpleHom K true b y) := by
  have hraw : Commute (simpleGeneratedHom K false a x).val (simpleGeneratedHom K true b y).val := by
    rw [simpleGeneratedHom_val, simpleGeneratedHom_val]
    cases a <;> cases b
    · exact (hne rfl).elim
    · change Commute (shortOrbit K (RingEquiv.refl K) false x.toAdd)
        (canonicalRoot rawData K true 1 y.toAdd)
      exact ((opposite_simple_commute K 0 1 (by decide) x.toAdd y.toAdd).mul_left
        (opposite_simple_commute K 2 1 (by decide) x.toAdd y.toAdd)).mul_left
          (opposite_simple_commute K 3 1 (by decide) x.toAdd y.toAdd)
    · change Commute (canonicalRoot rawData K false 1 x.toAdd)
        (shortOrbit K (RingEquiv.refl K) true y.toAdd)
      exact ((opposite_simple_commute K 1 0 (by decide) x.toAdd y.toAdd).mul_right
        (opposite_simple_commute K 1 2 (by decide) x.toAdd y.toAdd)).mul_right
          (opposite_simple_commute K 1 3 (by decide) x.toAdd y.toAdd)
    · exact (hne rfl).elim
  have hJ : Commute (simpleGeneratedHom K false a x) (simpleGeneratedHom K true b y) :=
    Subtype.ext hraw.eq
  exact hJ.map (generatedToOriginal K)

private theorem generated_simple_reflection (a : Bool) :
    let u := simpleGeneratedHom K false a (Multiplicative.ofAdd 1)
    let v := simpleGeneratedHom K true a (Multiplicative.ofAdd 1)
    (u * v⁻¹ * u) * u * (u * v⁻¹ * u)⁻¹ = v⁻¹ := by
  dsimp only
  have hinv : (simpleGeneratedHom K true a (Multiplicative.ofAdd 1))⁻¹ =
      simpleGeneratedHom K true a (Multiplicative.ofAdd (-1)) := (map_inv _ _).symm
  rw [hinv]
  apply Subtype.ext
  change ((simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val *
      (simpleGeneratedHom K true a (Multiplicative.ofAdd (-1))).val *
      (simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val) *
    (simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val *
    ((simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val *
      (simpleGeneratedHom K true a (Multiplicative.ofAdd (-1))).val *
      (simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val)⁻¹ =
        (simpleGeneratedHom K true a (Multiplicative.ofAdd (-1))).val
  have hword : canonicalWord rawData K (orbitWord a) =
      (simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val *
      (simpleGeneratedHom K true a (Multiplicative.ofAdd (-1))).val *
      (simpleGeneratedHom K false a (Multiplicative.ofAdd 1)).val := by
    simpa only [simpleGeneratedHom_val, orbitParameter] using orbit_word_parameter K (RingEquiv.refl K) a
  rw [←hword]
  exact simple_word_conjugates K a 1

private theorem mapped_rank_one_not_commute {G H : Type*} [Group G] [Group H]
    (f : G →* H) (u v : G) (hsep : f u ≠ (f v)⁻¹)
    (href : (u * v⁻¹ * u) * u * (u * v⁻¹ * u)⁻¹ = v⁻¹) : ¬Commute (f u) (f v) := by
  apply CFSGRankOneNoncommutation.not_commute _ _ hsep
  simpa only [map_mul, map_inv] using congrArg f href

theorem original_same_axis_not_commute (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.G₂ K)] (a : Bool) :
    ¬Commute (originalSimpleHom K false a (Multiplicative.ofAdd 1))
      (originalSimpleHom K true a (Multiplicative.ofAdd 1)) := by
  have hnonzero : originalSimpleHom K false a (Multiplicative.ofAdd 1) ≠ 1 := by
    intro he
    have hh := originalSimpleHom_injective K false a (he.trans (map_one _).symm)
    exact (one_ne_zero : (1 : K) ≠ 0) (congrArg (fun z : Multiplicative K => z.toAdd) hh)
  have hU : originalSimpleHom K false a (Multiplicative.ofAdd 1) ∈
      (originalPositiveSylow K p : Subgroup (CFSG.Models.Chevalley.Projective CartanMatrix.G₂ K)) := by
    rw [originalPositiveSylow_coe]
    exact ⟨_, simpleGeneratedHom_mem_rootPart K false a _, rfl⟩
  have hV : originalSimpleHom K true a (Multiplicative.ofAdd 1) ∈ originalNegative K :=
    ⟨_, simpleGeneratedHom_mem_rootPart K true a _, rfl⟩
  have hdisj : (originalPositiveSylow K p : Subgroup
      (CFSG.Models.Chevalley.Projective CartanMatrix.G₂ K)) ⊓ originalNegative K = ⊥ := by
    rw [←originalOppositeSylow_coe K p]
    exact original_opposite_sylows_disjoint K p
  have hsep : originalSimpleHom K false a (Multiplicative.ofAdd 1) ≠
      (originalSimpleHom K true a (Multiplicative.ofAdd 1))⁻¹ := by
    intro he
    have hm : originalSimpleHom K false a (Multiplicative.ofAdd 1) ∈
        (originalPositiveSylow K p : Subgroup (CFSG.Models.Chevalley.Projective CartanMatrix.G₂ K)) ⊓
          originalNegative K := ⟨hU, by rw [he]; exact (originalNegative K).inv_mem hV⟩
    rw [hdisj, Subgroup.mem_bot] at hm
    exact hnonzero hm
  exact mapped_rank_one_not_commute (generatedToOriginal K)
    (simpleGeneratedHom K false a (Multiplicative.ofAdd 1))
    (simpleGeneratedHom K true a (Multiplicative.ofAdd 1)) hsep (generated_simple_reflection K a)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalRankOneWitness
