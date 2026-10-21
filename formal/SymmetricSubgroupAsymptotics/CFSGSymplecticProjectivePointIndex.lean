import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootParameters
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
import SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper

/-! Actual projective point stabilizers in the elementary symplectic
central quotient. A moved point suffices for the upper index bound;
no transitivity or full symplectic-group recognition is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGProjectiveLinearPointAction
variable (K : Type*) [Field K]

abbrev NaturalPoints (r : ℕ) := Projectivization K (Index r → K)

abbrev naturalPointAction (r : ℕ) : MulAction (elementaryRootGroup K r) (NaturalPoints K r) :=
  MulAction.compHom (NaturalPoints K r)
    (linearEquiv.toMonoidHom.comp (elementaryRootGroup K r).subtype)

theorem center_fixes_natural_point (r : ℕ)
    (u : elementaryRootGroup K (r + 1))
    (hu : u ∈ Subgroup.center (elementaryRootGroup K (r + 1)))
    (p : NaturalPoints K (r + 1)) :
    letI := naturalPointAction K (r + 1)
    u • p = p := by
  letI := naturalPointAction K (r + 1)
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r u).mp hu
  change linearEquiv u.val • p = p
  rw [← Projectivization.mk_rep p, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨c, ?_⟩
  change c • p.rep = (u.val : Mat K (r + 1)) *ᵥ p.rep
  rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem terminal_root_moves_natural_point (r : ℕ) :
    letI := naturalPointAction K (r + 1)
    elementaryRoot K (r + 1) false (Fin.last r) 1 •
        CFSGProjectiveFrameCoordinates.basisPoint (F := K) (Sum.inr (Fin.last r) : Index (r + 1)) ≠
      CFSGProjectiveFrameCoordinates.basisPoint (F := K) (Sum.inr (Fin.last r) : Index (r + 1)) := by
  letI := naturalPointAction K (r + 1)
  intro h
  change linearEquiv (elementaryRoot K (r + 1) false (Fin.last r) 1).val •
      CFSGProjectiveFrameCoordinates.basisPoint (F := K) (Sum.inr (Fin.last r) : Index (r + 1)) = _ at h
  rw [CFSGProjectiveFrameCoordinates.basisPoint, Projectivization.smul_mk] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  change a • Pi.single (Sum.inr (Fin.last r)) (1 : K) =
    ((elementaryRoot K (r + 1) false (Fin.last r) 1).val : Mat K (r + 1)) *ᵥ
      Pi.single (Sum.inr (Fin.last r)) 1 at ha
  have he := congrFun ha (Sum.inl (Fin.last r))
  simpa [elementaryRoot, rootTransvection, rootMatrix, positive,
    Matrix.add_mulVec, Matrix.mulVec_single_one, Matrix.col, Matrix.single,
    Matrix.one_apply, Pi.single_apply] using he

theorem exists_proper_subgroup_of_natural_point_index [Finite K] (r : ℕ) :
    ∃ H : Subgroup (elementaryProjective K (r + 1)), H ≠ ⊤ ∧
      H.index ≤ Nat.card (NaturalPoints K (r + 1)) := by
  letI := naturalPointAction K (r + 1)
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  refine CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point
    pi (QuotientGroup.mk'_surjective _)
    (CFSGProjectiveFrameCoordinates.basisPoint (F := K) (Sum.inr (Fin.last r) : Index (r + 1)))
    ?_ (elementaryRoot K (r + 1) false (Fin.last r) 1) ?_
  · intro u hu
    rw [QuotientGroup.ker_mk'] at hu
    exact center_fixes_natural_point K r u hu _
  · exact terminal_root_moves_natural_point K r

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
