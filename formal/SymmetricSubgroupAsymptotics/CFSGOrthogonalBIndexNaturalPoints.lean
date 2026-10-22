import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexRootSubgroup
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
import SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! One actual moved natural point gives the odd B projective quotient
a proper subgroup. No transitivity, singular-point formula or full
orthogonal-group identification is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexNaturalPoints
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationShortArrays CFSGProjectiveLinearPointAction
open CFSGReduction PrimitiveSocleRawStructure
variable (K : Type) [Field K]

abbrev NaturalPoints (r : ℕ) := Projectivization K (Index r → K)

abbrev naturalPointAction (r : ℕ) : MulAction (elementaryRootGroup K r) (NaturalPoints K r) :=
  MulAction.compHom (NaturalPoints K r)
    (linearEquiv.toMonoidHom.comp (elementaryRootGroup K r).subtype)

theorem center_fixes_point (h2 : (2 : K) ≠ 0) (s : ℕ)
    (u : elementaryRootGroup K (s + 3))
    (hu : u ∈ Subgroup.center (elementaryRootGroup K (s + 3)))
    (p : NaturalPoints K (s + 3)) :
    letI := naturalPointAction K (s + 3)
    u • p = p := by
  letI := naturalPointAction K (s + 3)
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) h2 u).mp hu
  change linearEquiv u.val • p = p
  rw [← Projectivization.mk_rep p, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨c, ?_⟩
  change c • p.rep = (u.val : Mat K (s + 3)) *ᵥ p.rep
  rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem terminal_moves_middle_point (s : ℕ) :
    letI := naturalPointAction K (s + 3)
    betaElement K s 1 • CFSGProjectiveFrameCoordinates.basisPoint (F := K) (middle (s + 3)) ≠
      CFSGProjectiveFrameCoordinates.basisPoint (F := K) (middle (s + 3)) := by
  letI := naturalPointAction K (s + 3)
  intro h
  change linearEquiv (betaElement K s 1).val •
    CFSGProjectiveFrameCoordinates.basisPoint (F := K) (middle (s + 3)) = _ at h
  rw [CFSGProjectiveFrameCoordinates.basisPoint, Projectivization.smul_mk] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  change a • Pi.single (middle (s + 3)) (1 : K) =
    ((betaElement K s 1).val : Mat K (s + 3)) *ᵥ Pi.single (middle (s + 3)) 1 at ha
  have he := congrFun ha (pos (s + 3) (lastIndex s))
  simpa [betaElement_val, betaUnit, shortUnit_val, shortArray, shortSecond,
    Matrix.add_mulVec, Matrix.mulVec_single_one, Matrix.col, Matrix.single_apply,
    Matrix.one_apply, Pi.single_apply, pos, neg, middle, paired] using he

theorem exists_proper_subgroup_of_natural_point_index [Finite K]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    ∃ H : Subgroup (elementaryProjective K (s + 3)), H ≠ ⊤ ∧
      H.index ≤ Nat.card (NaturalPoints K (s + 3)) := by
  letI := naturalPointAction K (s + 3)
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))
  refine CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point
    q (QuotientGroup.mk'_surjective _)
    (CFSGProjectiveFrameCoordinates.basisPoint (F := K) (middle (s + 3)))
    ?_ (betaElement K s 1) (terminal_moves_middle_point K s)
  intro u hu
  change u ∈ (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))).ker at hu
  rw [QuotientGroup.ker_mk'] at hu
  exact center_fixes_point K h2 s u hu _

theorem naturalPoints_card_mul_units [Finite K] (r : ℕ) :
    Nat.card (NaturalPoints K r) * (Nat.card K - 1) = Nat.card K ^ (2 * r + 1) - 1 := by
  simpa only [NaturalPoints, Nat.card_fun, Nat.card_sum, Nat.card_fin, Nat.card_unique, two_mul]
    using (Projectivization.card K (Index r → K)).symm

theorem elementary_leastProperIndex_mul_field_sub_one [Finite K]
    (h2 : (2 : K) ≠ 0) (s ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (s + 3)) ell) :
    ell * (Nat.card K - 1) ≤ Nat.card K ^ (2 * (s + 3) + 1) - 1 := by
  obtain ⟨H, hH, hi⟩ := exists_proper_subgroup_of_natural_point_index K h2 s
  exact (Nat.mul_le_mul_right (Nat.card K - 1) ((hell.2 H hH).trans hi)).trans_eq
    (naturalPoints_card_mul_units K (s + 3))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexNaturalPoints
