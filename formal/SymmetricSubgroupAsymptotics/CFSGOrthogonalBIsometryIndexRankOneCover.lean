import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialFormGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneDiagonal
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneStabilizer

/-! A one-sided elementary coset cover of the actual rank-one special
isometry group. We normalize the INVERSE image of the first vector;
this avoids any assumption that the elementary subgroup is normal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneCover
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup CFSGOrthogonalBIndexForm
open CFSGOrthogonalBIsometryIndexRankOneOrbit CFSGOrthogonalBIsometryIndexRankOneDiagonal
open CFSGOrthogonalBIsometryIndexRankOneStabilizer
variable (K : Type) [Field K]

theorem diagonal_first (a : Kˣ) :
    (diagonalHom K a : Mat K 1) *ᵥ Pi.single (pos 1 0) 1 =
      (a : K) • Pi.single (pos 1 0) 1 := by
  rw [diagonalHom_val, Matrix.mulVec_single_one]
  funext i
  rcases i with (i | i) | i
  · fin_cases i
    simp [diagonalWeights, pos, Matrix.col]
  · fin_cases i
    simp [diagonalWeights, pos, Matrix.col]
  · cases i
    simp [diagonalWeights, pos, Matrix.col]

theorem one_sided_cover (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (g : specialFormUnits K 1) :
    ∃ a : Kˣ, (diagonalHom K a)⁻¹ * g.val ∈ elementaryRootGroup K 1 := by
  let e : Index 1 → K := Pi.single (pos 1 0) 1
  let gi : formUnits K 1 := ⟨g.val⁻¹, ((specialFormUnits K 1).inv_mem g.property).1⟩
  have he : e ≠ 0 := by
    intro hh
    have hc := congrFun hh (pos 1 0)
    simp [e] at hc
  have hv : ((g.val⁻¹ : (Mat K 1)ˣ) : Mat K 1) *ᵥ e ≠ 0 := by
    intro hh
    have hc := congrArg (fun v : Index 1 → K => (g.val : Mat K 1) *ᵥ v) hh
    dsimp only at hc
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at hc
    exact he hc
  have hs : (gram K 1).toBilin' (((g.val⁻¹ : (Mat K 1)ˣ) : Mat K 1) *ᵥ e)
      (((g.val⁻¹ : (Mat K 1)ˣ) : Mat K 1) *ᵥ e) = 0 := by
    rw [pairing_invariant K 1 gi]
    simp [e, Matrix.toBilin'_apply, gram, pos]
  obtain ⟨a, t, ht, ha⟩ := exists_scalar_normalize K h2 _ hv hs
  let tU : Kˣ := Units.mk0 t ht
  have haction : ((g.val : Mat K 1) * ((a.val⁻¹ : (Mat K 1)ˣ) : Mat K 1)) *ᵥ e = t⁻¹ • e := by
    have hleft := congrArg (fun v : Index 1 → K =>
      ((a.val⁻¹ : (Mat K 1)ˣ) : Mat K 1) *ᵥ v) ha
    dsimp only at hleft
    simp only [Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul, Matrix.one_mulVec,
      Matrix.mulVec_smul] at hleft
    have hh := congrArg (fun v : Index 1 → K => (g.val : Mat K 1) *ᵥ v) hleft
    dsimp only at hh
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec,
      Matrix.mulVec_smul] at hh
    have hscaled := congrArg (fun v : Index 1 → K => t⁻¹ • v) hh
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul,
      Matrix.mulVec_mulVec] using hscaled.symm
  let b : (Mat K 1)ˣ := diagonalHom K tU * g.val * a.val⁻¹
  have hb : b ∈ specialFormUnits K 1 := by
    apply (specialFormUnits K 1).mul_mem
    · apply (specialFormUnits K 1).mul_mem
      · exact (mem_specialFormUnits_iff K 1 _).mpr
          ⟨diagonalHom_preserves K tU, diagonalHom_det K tU⟩
      · exact g.property
    · exact (specialFormUnits K 1).inv_mem
        (elementary_le_specialFormUnits K p h2 1 a.property)
  have hfix : (b : Mat K 1) *ᵥ e = e := by
    change (((diagonalHom K tU : Mat K 1) * (g.val : Mat K 1)) *
      ((a.val⁻¹ : (Mat K 1)ˣ) : Mat K 1)) *ᵥ e = e
    rw [mul_assoc, ← Matrix.mulVec_mulVec, haction, Matrix.mulVec_smul, diagonal_first]
    change t⁻¹ • (t • e) = e
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  obtain ⟨s, hs⟩ := first_vector_stabilizer_elementary K h2 (b : Mat K 1)
    ((mem_specialFormUnits_iff K 1 b).mp hb).1
    ((mem_specialFormUnits_iff K 1 b).mp hb).2 hfix
  have hbe : b ∈ elementaryRootGroup K 1 := by
    have heq : s.val = b := Units.ext hs
    exact heq ▸ s.property
  refine ⟨tU⁻¹, ?_⟩
  have hprod := (elementaryRootGroup K 1).mul_mem hbe a.property
  have heq : b * a.val = diagonalHom K tU * g.val := by dsimp [b]; group
  rw [heq] at hprod
  simpa only [map_inv, inv_inv] using hprod

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneCover
