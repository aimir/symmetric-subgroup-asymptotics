import SymmetricSubgroupAsymptotics.CFSGSymplecticSLDoubleEmbedding
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
import SymmetricSubgroupAsymptotics.CFSGSymplecticAllNaturalTransvections
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointTailAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticTerminalTorus

/-! An actual subgroup containing the SL double and one positive long
root contains every transvection on the upper isotropic half. No full
symplectic image or recognition theorem is asserted. The paired-coordinate
corollary uses the actual change `(u,v) ↦ (v,-u)`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUpperTransvectionSubgroup
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticHeisenbergVectorAction CFSGSymplecticBinaryPointTailAction

variable (K : Type) [Field K]

theorem terminal_positive_natural (r : ℕ) (a : K) (x : Index (r+1) → K) :
    ((elementaryRoot K (r+1) false (Fin.last r) a).val : Mat K (r+1)) *ᵥ x =
      transvection (r+1) (Pi.single (Sum.inl (Fin.last r)) 1) a x := by
  rw [terminal_positive_coe]
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, transvection_apply, pairing_pos_basis_left]
  funext j
  simp [Function.update_apply, Pi.single_apply]

theorem exists_upper_natural (r : ℕ) (hr : 0 < r)
    (J : Subgroup (elementaryRootGroup K (r+1)))
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin (r+1)) K,
      CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K (r+1) A ∈ J)
    (hlong : elementaryRoot K (r+1) false (Fin.last r) 1 ∈ J)
    (v : Fin (r+1) → K) (hv : v ≠ 0) :
    ∃ g ∈ J, ∀ x : Index (r+1) → K,
      (g.val : Mat K (r+1)) *ᵥ x =
        transvection (r+1) (Sum.elim v 0) 1 x := by
  let e : Fin (r+1) → K := Pi.single (Fin.last r) 1
  have he : e ≠ 0 := by intro h; have hh := congrFun h (Fin.last r); simpa [e] using hh
  obtain ⟨A,hA⟩ := CFSGTypeAVectorTransitivity.exists_map_nonzero
    (0 : Fin (r+1)) (Fin.last r) (by
      intro h
      have hh : 0 = r := congrArg Fin.val h
      omega)
    e v he hv
  let g := CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K (r+1) A
  let t := elementaryRoot K (r+1) false (Fin.last r) (1 : K)
  let E : Index (r+1) → K := Pi.single (Sum.inl (Fin.last r)) 1
  have hE : E = Sum.elim e 0 := by
    funext j
    cases j <;> simp [E,e,Pi.single_apply]
  have hgE : (g.val : Mat K (r+1)) *ᵥ E = Sum.elim v 0 := by
    change CFSGOrthogonalDGenerationSLDouble.doubleMatrix K (r+1) A *ᵥ E = _
    rw [hE, CFSGOrthogonalDGenerationSLDouble.doubleMatrix, Matrix.fromBlocks_mulVec]
    have hAv : A.val *ᵥ e = v := hA
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero, zero_add] using
      congrArg (fun w : Fin (r+1) → K => Sum.elim w (0 : Fin (r+1) → K)) hAv
  refine ⟨g*t*g⁻¹, J.mul_mem (J.mul_mem (hSL A) hlong) (J.inv_mem (hSL A)), ?_⟩
  intro x
  have hi : (g.val : Mat K (r+1)) *ᵥ ((↑(g.val⁻¹) : Mat K (r+1)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hp := elementary_preserves_pairing (r+1) g E
    ((↑(g.val⁻¹) : Mat K (r+1)) *ᵥ x)
  change pairing (r+1) ((g.val : Mat K (r+1)) *ᵥ E)
    ((g.val : Mat K (r+1)) *ᵥ ((↑(g.val⁻¹) : Mat K (r+1)) *ᵥ x)) = _ at hp
  rw [hgE, hi] at hp
  change (((g.val : Mat K (r+1)) * (t.val : Mat K (r+1))) *
    (↑(g.val⁻¹) : Mat K (r+1))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    terminal_positive_natural, transvection_apply, Matrix.mulVec_add,
    Matrix.mulVec_smul, hi]
  change x + (1 * pairing (r+1) E ((↑(g.val⁻¹) : Mat K (r+1)) *ᵥ x)) •
    ((g.val : Mat K (r+1)) *ᵥ E) = _
  rw [← hp, hgE]
  rfl

theorem upper_natural_in_paired_coordinates [CharP K 2]
    (m : ℕ) (v : Fin m → K) (x : (Fin m → K) × (Fin m → K)) :
    (vectorEquiv K m).symm
      (transvection m (Sum.elim v 0) 1 (vectorEquiv K m x)) =
      BinaryQuadraticRefinementTransvections.transvectionMap (0,v) x := by
  rw [transvection_apply, one_mul]
  have hp : pairing m (Sum.elim v (0 : Fin m → K))
      (vectorEquiv K m x) = dotProduct v x.1 := by
    change pairing m (Sum.elim v (0 : Fin m → K))
      (Sum.elim x.2 (-x.1)) = _
    simp [pairing, dotProduct, CharTwo.neg_eq]
  rw [hp]
  apply Prod.ext <;> funext i <;>
    simp [vectorEquiv, BinaryQuadraticRefinementTransvections.transvectionMap,
      BinaryQuadraticRefinementTransvections.polar,
      dotProduct_comm, CharTwo.neg_eq]

theorem exists_paired_Y_transvection [CharP K 2]
    (r : ℕ) (hr : 0 < r) (J : Subgroup (elementaryRootGroup K (r+1)))
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin (r+1)) K,
      CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K (r+1) A ∈ J)
    (hlong : elementaryRoot K (r+1) false (Fin.last r) 1 ∈ J)
    (v : Fin (r+1) → K) :
    ∃ g : J, ∀ x : (Fin (r+1) → K) × (Fin (r+1) → K),
      vectorLinearHom K (r+1) g.val x =
        BinaryQuadraticRefinementTransvections.transvectionMap (0,v) x := by
  by_cases hv : v = 0
  · subst v
    refine ⟨1, ?_⟩
    intro x
    simp [BinaryQuadraticRefinementTransvections.transvectionMap,
      BinaryQuadraticRefinementTransvections.polar]
  · obtain ⟨g,hg,hact⟩ := exists_upper_natural K r hr J hSL hlong v hv
    refine ⟨⟨g,hg⟩, ?_⟩
    intro x
    rw [vectorLinearHom_apply, hact]
    exact upper_natural_in_paired_coordinates K (r+1) v x

end SymmetricSubgroupAsymptotics.CFSGSymplecticUpperTransvectionSubgroup
