import SymmetricSubgroupAsymptotics.CFSGSymplecticSignedLongCoverage
import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialLongRoots

/-! Every natural coordinate long-root group is actually inside the
literal elementary C subgroup. The proof uses signed Coxeter transport
of the original root word, not a full-Sp equality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines CFSGMonomialUnitRootAction

def coordinateLongUnit (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin (r + 1)) (a : K) : (Mat K (r + 1))ˣ :=
  transvectionUnit (coordinatePoint r side i) (coordinatePoint r (!side) i)
    (by cases side <;> intro h <;> cases h) a

theorem coordinateLongUnit_mem (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin (r + 1)) (a : K) : coordinateLongUnit K r side i a ∈ elementaryRootGroup K (r + 1) := by
  have h0 : HasRootLine (elementaryRootGroup K (r + 1)) (coordinateLongRootMatrix K r false 0) := by
    intro b
    refine ⟨(firstLongRoot K r b).val, (firstLongRoot K r b).property, ?_⟩
    simpa only [coordinateLongRootMatrix, coordinatePoint, Bool.not_false,
      Bool.false_eq_true, if_false, if_true, Matrix.transvection,
      Matrix.smul_single, smul_eq_mul, mul_one] using firstLongRoot_coe K r b
  have hc := coordinate_long_coverage K r (elementaryRootGroup K (r + 1))
    (coxeterWeyl K r).property h0
  obtain ⟨u, hu, he⟩ := hc side i a
  have hue : u = coordinateLongUnit K r side i a := by
    apply Units.ext
    simpa only [coordinateLongUnit, transvectionUnit_val, coordinateLongRootMatrix,
      Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one] using he
  exact hue ▸ hu

def coordinateTorusUnit (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) (g : Kˣ) :
    (Mat K (r + 1))ˣ :=
  coordinateLongUnit K r false i ((g : K) - 1) * coordinateLongUnit K r true i 1 *
    coordinateLongUnit K r false i ((g : K)⁻¹ - 1) * coordinateLongUnit K r true i (-(g : K))

theorem coordinateTorusUnit_mem (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) (g : Kˣ) :
    coordinateTorusUnit K r i g ∈ elementaryRootGroup K (r + 1) :=
  (elementaryRootGroup K (r + 1)).mul_mem
    ((elementaryRootGroup K (r + 1)).mul_mem
      ((elementaryRootGroup K (r + 1)).mul_mem
        (coordinateLongUnit_mem K r false i _) (coordinateLongUnit_mem K r true i _))
      (coordinateLongUnit_mem K r false i _)) (coordinateLongUnit_mem K r true i _)

theorem coordinateTorusUnit_val (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) (g : Kˣ) :
    (coordinateTorusUnit K r i g : Mat K (r + 1)) =
      Matrix.diagonal (coordinateTorusDiagonal K r i g) := by
  change Matrix.transvection (Sum.inl i) (Sum.inr i) ((g : K) - 1) *
    Matrix.transvection (Sum.inr i) (Sum.inl i) 1 *
    Matrix.transvection (Sum.inl i) (Sum.inr i) ((g : K)⁻¹ - 1) *
    Matrix.transvection (Sum.inr i) (Sum.inl i) (-(g : K)) = _
  exact CFSGTypeAElementaryMatrices.diagonal_pair (by intro h; cases h) (g : K) (Units.ne_zero g)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
