import SymmetricSubgroupAsymptotics.BinaryPhysicalPairEnvelope
import SymmetricSubgroupAsymptotics.FusionKernelAssembly

/-! Canonical numerical parameters of one fixed physical pair certificate.
The original cover and cut determine the moment degree. The actual physical
width and certified fixed dimension determine a positive gap parameter.
These choices install the proved envelope in the existing local factor;
the translation and first-cohomology constant stays outside the moment.
No all-axis selection, physical owner coverage or global sum is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate

section General

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryPhysicalPairCertificate U N)

/-- The actual quotient-cover degree and the retained binary-marker degree. -/
def prefixDegree : ℕ :=
  C.localCertificate.coverDegree + 2*C.localCertificate.cutDimension

/-- The exact gap after the certified fixed-space contribution. -/
def gapParameter : ℝ :=
  ((w : ℝ) - (C.prefixDegree : ℝ) - 4*(C.localCertificate.fixedDimension : ℝ))/16

/-- The physical degree is forced by the original frame equivalence. -/
theorem physical_degree : 2*C.pairCount = w := by
  simpa only [Nat.card_prod, Nat.card_fin, Nat.card_zmod, Nat.mul_comm] using
    Nat.card_congr C.frame.frame

/-- Bind the finite certificate's width to the literal original action. -/
theorem certified_gap :
    C.prefixDegree + 4*C.localCertificate.fixedDimension < w := by
  simpa only [prefixDegree, C.physical_width, Nat.card_fin] using C.localCertificate.gap

/-- The integer certificate supplies a uniform positive rational gap. -/
theorem gapParameter_ge_one_sixteenth : (1 : ℝ)/16 ≤ C.gapParameter := by
  have hn : C.prefixDegree + 4*C.localCertificate.fixedDimension + 1 ≤ w :=
    Nat.succ_le_of_lt C.certified_gap
  have hr : (C.prefixDegree : ℝ) + 4*(C.localCertificate.fixedDimension : ℝ) + 1 ≤
      (w : ℝ) := by exact_mod_cast hn
  unfold gapParameter
  linarith

theorem gapParameter_pos : 0 < C.gapParameter :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/16) C.gapParameter_ge_one_sixteenth

/-- This equality keeps the full certified Schur exponent, with no loss
or absorption of the translation/cohomology factors into the weight. -/
theorem gapParameter_coefficient :
    ((w : ℝ) - (C.prefixDegree : ℝ) - 16*C.gapParameter)/8 =
      (C.localCertificate.fixedDimension : ℝ)/2 := by
  unfold gapParameter
  ring

/-- The canonical parameters reproduce the actual envelope factor exactly. -/
theorem fusionLocalFactor_eq (b : ℕ) :
    fusionLocalFactor b C.pairCount C.prefixDegree C.liftConstant C.gapParameter =
      C.liftConstant * (2 : ℝ)^((C.localCertificate.fixedDimension : ℝ)/2*(b : ℝ)) := by
  unfold fusionLocalFactor
  rw [C.physical_degree, C.gapParameter_coefficient]

/-- All moments use the same fixed certificate and complete original J. -/
theorem prefixDegree_moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J^q) ≤
      (subgroupCount (b+q*C.prefixDegree) : ℝ) :=
  C.momentWeight_moment_le b q

theorem original_survivingEpiCount_le_localFactor {b : ℕ} (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      fusionLocalFactor b C.pairCount C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  rw [C.fusionLocalFactor_eq b]
  exact C.original_survivingEpiCount_le hU P J

end General

section AmbientDegree

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))} {N : Subgroup U} [N.Normal]
    (C : BinaryPhysicalPairCertificate U N)

/-- Ambient-degree form for the existing physical kernel theorem. No
dependent transport from the certificate's pair-label type is needed. -/
theorem fusionLocalFactor_eq_ambient (b : ℕ) :
    fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter =
      C.liftConstant * (2 : ℝ)^((C.localCertificate.fixedDimension : ℝ)/2*(b : ℝ)) := by
  unfold fusionLocalFactor
  rw [C.gapParameter_coefficient]

/-- The exact local input to original-weight fusion, with the ambient h
and all remaining numerical parameters supplied by this certificate. -/
theorem original_survivingEpiCount_le_localFactor_ambient {b : ℕ} (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  rw [C.fusionLocalFactor_eq_ambient b]
  exact C.original_survivingEpiCount_le hU P J

end AmbientDegree

end SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate
