import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeProjection
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStandardCoordinates

/-! Literal opposite coordinate space and the two maximal coordinate halves.
The opposite is obtained by an actual linear reversal, and its dimension,
isotropy and disjointness are checked from the coordinate support. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUnitaryParameters

def unitaryCoordinateReversal (q : CFSG.PrimePower) (r : ℕ) :
    (Fin (r + 1) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (r + 1) → q.Extension 2) where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := by funext i; exact congrArg x (Fin.rev_rev i)
  right_inv x := by funext i; exact congrArg x (Fin.rev_rev i)
  map_add' x y := rfl
  map_smul' a x := rfl

def unitaryOppositeSingularSpace (q : CFSG.PrimePower) (r : ℕ) :
    Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2) :=
  (unitaryStandardSingularSpace q r).map (unitaryCoordinateReversal q r).toLinearMap

theorem unitaryOppositeSingularSpace_mem_iff (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) :
    x ∈ unitaryOppositeSingularSpace q r ↔
      ∀ i, r < 2 * i.rev.val + 1 → x i = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ i hi
    exact hy i.rev hi
  · intro hx
    refine ⟨unitaryCoordinateReversal q r x, ?_, ?_⟩
    · intro i hi
      exact hx i.rev (by simpa only [Fin.rev_rev] using hi)
    · exact (unitaryCoordinateReversal q r).apply_symm_apply x

theorem unitaryOppositeProjection_mem (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) :
    unitaryOppositeProjection q r x ∈ unitaryOppositeSingularSpace q r := by
  rw [unitaryOppositeSingularSpace_mem_iff]
  intro i hi
  exact if_pos hi

theorem unitaryOppositeProjection_eq_self (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) (hx : x ∈ unitaryOppositeSingularSpace q r) :
    unitaryOppositeProjection q r x = x := by
  funext i
  by_cases hi : r < 2 * i.rev.val + 1
  · rw [unitaryOppositeProjection, if_pos hi,
      (unitaryOppositeSingularSpace_mem_iff q r x).mp hx i hi]
  · exact if_neg hi

theorem unitaryOppositeSingularSpace_pair_zero (q : CFSG.PrimePower) (r : ℕ)
    (x y : Fin (r + 1) → q.Extension 2)
    (hx : x ∈ unitaryOppositeSingularSpace q r) (hy : y ∈ unitaryOppositeSingularSpace q r) :
    unitaryNaturalPair q r x y = 0 := by
  have h := unitaryOppositeProjection_pair_zero q r x y
  rwa [unitaryOppositeProjection_eq_self q r x hx,
    unitaryOppositeProjection_eq_self q r y hy] at h

theorem unitaryOppositeSingularSpace_finrank (q : CFSG.PrimePower) (r : ℕ) :
    Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q r) = (r + 1) / 2 := by
  rw [unitaryOppositeSingularSpace, LinearEquiv.finrank_map_eq,
    unitaryStandardSingularSpace_finrank]

theorem unitaryStandard_opposite_disjoint (q : CFSG.PrimePower) (r : ℕ) :
    Disjoint (unitaryStandardSingularSpace q r) (unitaryOppositeSingularSpace q r) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  funext i
  by_cases hi : r < 2 * i.val + 1
  · exact hx i hi
  · apply (unitaryOppositeSingularSpace_mem_iff q r x).mp hy i
    have hv : i.rev.val = r - i.val := by rw [Fin.val_rev]; omega
    have hib := i.isLt
    omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
