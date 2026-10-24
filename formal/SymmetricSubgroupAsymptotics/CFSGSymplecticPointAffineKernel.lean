import SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineHom

/-! The actual point-to-affine kernel injects into one original matrix
entry. Equal entries give equal partner images; the ratio then fixes
the first hyperbolic pair and has trivial tail. Checked first-pair
faithfulness proves equality. This includes tail rank zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineKernel
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticTransvectionGeometry CFSGSymplecticPointTailCoordinates
open CFSGSymplecticPointAffineCoordinates CFSGSymplecticPointAffineHom
open LinearSemidirectCommutingFibres
variable (K : Type) [Field K]

theorem partner_image_of_zero_column (r : ℕ) (g : pointStabilizer K r)
    (hg : partnerColumn K r (g.val.val : Mat K (r+1)) = 0) :
    (g.val.val : Mat K (r+1)) *ᵥ Pi.single (Sum.inr 0) 1 =
      (g.val.val : Mat K (r+1)) (Sum.inl 0) (Sum.inr 0) •
        Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  rcases index_head_or_tail r i with rfl | rfl | ⟨i,rfl⟩
  · simp only [Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_apply, reduceCtorEq, if_false, mul_one, add_zero]
  · have hn := fixed_positive_basis_row (r+1)
      (g.val.val : Mat K (r+1)) (elementary_preserves_pairing (r+1) g.val)
      0 g.property (Sum.inr 0)
    simpa only [Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_apply, reduceCtorEq, if_false, mul_zero, zero_add]
      using hn
  · have ht := congrFun hg i
    change (g.val.val : Mat K (r+1)) (tailIndex r i) (Sum.inr 0) = 0 at ht
    cases i <;> simpa [Matrix.col_apply, tailIndex, Pi.single_apply] using ht

private theorem kernel_layers (r : ℕ) (g : (pointAffineHom K r).ker) :
    partnerColumn K r (g.val.val.val : Mat K (r+1)) = 0 ∧
      pointTailHom K r g.val = 1 := by
  have he : pointAffineHom K r g.val = 1 := g.property
  have hv := congrArg
    (fun a : AffineGroup (naturalLinearHom K r) => a.left.toAdd) he
  have ht := congrArg
    (fun a : AffineGroup (naturalLinearHom K r) => a.right) he
  exact ⟨hv,ht⟩

def kernelCoordinate (r : ℕ) (g : (pointAffineHom K r).ker) : K :=
  (g.val.val.val : Mat K (r+1)) (Sum.inl 0) (Sum.inr 0)

theorem kernelCoordinate_injective (r : ℕ) :
    Function.Injective (kernelCoordinate K r) := by
  intro g h hc
  obtain ⟨hgv,hgt⟩ := kernel_layers K r g
  obtain ⟨hhv,hht⟩ := kernel_layers K r h
  have hpartner : (g.val.val.val : Mat K (r+1)) *ᵥ Pi.single (Sum.inr 0) 1 =
      (h.val.val.val : Mat K (r+1)) *ᵥ Pi.single (Sum.inr 0) 1 := by
    rw [partner_image_of_zero_column K r g.val hgv,
      partner_image_of_zero_column K r h.val hhv]
    exact congrArg (fun c : K => c • (Pi.single (Sum.inl 0) 1 : Index (r+1) → K) +
      Pi.single (Sum.inr 0) 1) hc
  let z : pointStabilizer K r := g.val⁻¹*h.val
  have hzf : (z.val.val : Mat K (r+1)) *ᵥ Pi.single (Sum.inr 0) 1 =
      Pi.single (Sum.inr 0) 1 := by
    change (((g.val⁻¹).val.val : Mat K (r+1)) *
      (h.val.val.val : Mat K (r+1))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ← hpartner]
    rw [Matrix.mulVec_mulVec]
    have he := congrArg (fun a : pointStabilizer K r =>
      (a.val.val : Mat K (r+1))) (inv_mul_cancel g.val)
    change ((g.val⁻¹).val.val : Mat K (r+1)) *
      (g.val.val.val : Mat K (r+1)) = 1 at he
    rw [he, Matrix.one_mulVec]
  have hzt : pointTailHom K r z = 1 := by
    dsimp only [z]
    rw [map_mul, map_inv, hgt, hht, inv_one, one_mul]
  have htail : tailMatrix r (z.val.val : Mat K (r+1)) = 1 :=
    congrArg (fun a : elementaryRootGroup K r => (a.val : Mat K r)) hzt
  have hzraw : (z.val.val : Mat K (r+1)) = 1 :=
    eq_of_same_tail r _ _ (elementary_preserves_pairing (r+1) z.val)
      (by intro v w; rw [Matrix.one_mulVec, Matrix.one_mulVec])
      ⟨z.property,hzf⟩ ⟨Matrix.one_mulVec _,Matrix.one_mulVec _⟩
      (htail.trans (tailMatrix_one r).symm)
  have hz : z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hzraw
  have hgh : g.val = h.val := inv_mul_eq_one.mp hz
  exact Subtype.ext hgh

theorem kernel_card_le [Finite K] (r : ℕ) :
    Nat.card (pointAffineHom K r).ker ≤ Nat.card K :=
  Nat.card_le_card_of_injective (kernelCoordinate K r) (kernelCoordinate_injective K r)

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineKernel
