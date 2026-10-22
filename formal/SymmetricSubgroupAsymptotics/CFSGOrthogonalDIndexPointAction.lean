import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
import SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper

/-! Actual projective point stabilizers in the original elementary D
central quotient. A single original chain root moves a point, so a
proper stabilizer supplies the upper index bound. No transitivity or
identification with a full orthogonal group is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPointAction
open CFSGOrthogonalDSerreMatrices CFSGProjectiveLinearPointAction
variable (K : Type*) [Field K]

abbrev NaturalPoints (r : ℕ) := Projectivization K (Index r → K)

abbrev naturalPointAction (r : ℕ) : MulAction (elementaryRootGroup K r) (NaturalPoints K r) :=
  MulAction.compHom (NaturalPoints K r)
    (linearEquiv.toMonoidHom.comp (elementaryRootGroup K r).subtype)

theorem center_fixes_natural_point (s : ℕ) (u : elementaryRootGroup K (s + 4))
    (hu : u ∈ Subgroup.center (elementaryRootGroup K (s + 4)))
    (p : NaturalPoints K (s + 4)) :
    letI := naturalPointAction K (s + 4)
    u • p = p := by
  letI := naturalPointAction K (s + 4)
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) u).mp hu
  change linearEquiv u.val • p = p
  rw [← Projectivization.mk_rep p, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨c, ?_⟩
  change c • p.rep = (u.val : Mat K (s + 4)) *ᵥ p.rep
  rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]

def firstRoot (s : ℕ) : elementaryRootGroup K (s + 4) :=
  ⟨rootTransvection K (s + 4) false 0 1, rootTransvection_mem K (s + 4) false 0 1⟩

def movedPoint (s : ℕ) : NaturalPoints K (s + 4) :=
  CFSGProjectiveFrameCoordinates.basisPoint (F := K)
    (Sum.inl (⟨1, by omega⟩ : Fin (s + 4)) : Index (s + 4))

theorem first_root_moves_point (s : ℕ) :
    letI := naturalPointAction K (s + 4)
    firstRoot K s • movedPoint K s ≠ movedPoint K s := by
  letI := naturalPointAction K (s + 4)
  intro h
  change linearEquiv (firstRoot K s).val • movedPoint K s = movedPoint K s at h
  rw [movedPoint, CFSGProjectiveFrameCoordinates.basisPoint, Projectivization.smul_mk] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  change a • Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (s + 4))) (1 : K) =
    ((firstRoot K s).val : Mat K (s + 4)) *ᵥ
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (s + 4))) 1 at ha
  have he := congrFun ha (Sum.inl (0 : Fin (s + 4)))
  have hchain : (0 : Fin (s + 4)).val + 1 < s + 4 := by change 0 + 1 < s + 4; omega
  have hne : (0 : Fin (s + 4)) ≠ ⟨1, by omega⟩ := by simp
  simp [firstRoot, rootTransvection, rootMatrix, positive, hchain,
    Matrix.add_mulVec, Matrix.mulVec_single_one, Matrix.col, Matrix.single,
    Matrix.one_apply, Pi.single_apply, hne, Ne.symm hne] at he

theorem exists_proper_subgroup_of_natural_point_index [Finite K] (s : ℕ) :
    ∃ H : Subgroup (elementaryProjective K (s + 4)), H ≠ ⊤ ∧
      H.index ≤ Nat.card (NaturalPoints K (s + 4)) := by
  letI := naturalPointAction K (s + 4)
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))
  refine CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point pi
    (QuotientGroup.mk'_surjective _) (movedPoint K s) ?_ (firstRoot K s) ?_
  · intro u hu
    change u ∈ (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))).ker at hu
    rw [QuotientGroup.ker_mk'] at hu
    exact center_fixes_natural_point K s u hu _
  · exact first_root_moves_point K s

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPointAction
