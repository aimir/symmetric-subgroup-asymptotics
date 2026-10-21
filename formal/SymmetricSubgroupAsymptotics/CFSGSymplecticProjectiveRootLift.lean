import SymmetricSubgroupAsymptotics.CFSGSymplecticActualRootStabilizers
import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionGeometry
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter

/-! Equality of two actual natural transvections in the original
central quotient lifts to equality of the SAME elementary elements.
Their common nonzero fixed vector rules out a nontrivial scalar. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def pairingDual (r : ℕ) (v : Index r → K) : Module.Dual K (Index r → K) where
  toFun x := pairing r v x
  map_add' x y := pairing_add_right r v x y
  map_smul' a x := by simpa only [smul_eq_mul, RingHom.id_apply] using pairing_smul_right r a v x

theorem actualNaturalRootElement_eq_of_projective_eq (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (a b : K)
    (he : QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
        (actualNaturalRootElement r hr v a) =
      QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
        (actualNaturalRootElement r hr w b)) :
    actualNaturalRootElement r hr v a = actualNaturalRootElement r hr w b := by
  let V := actualNaturalRootElement r hr v a
  let W := actualNaturalRootElement r hr w b
  have hc : V / W ∈ Subgroup.center (elementaryRootGroup K (r + 1)) :=
    QuotientGroup.eq_iff_div_mem.mp he
  obtain ⟨c, hcent⟩ := (elementaryRootGroup_center_iff_scalar K r (V / W)).mp hc
  have hm : (V.val : Mat K (r + 1)) = c • (W.val : Mat K (r + 1)) := by
    have h := congrArg (fun g : elementaryRootGroup K (r + 1) => (g.val : Mat K (r + 1)))
      (div_mul_cancel V W).symm
    change (V.val : Mat K (r + 1)) = ((V / W).val : Mat K (r + 1)) * (W.val : Mat K (r + 1)) at h
    rw [hcent, Matrix.smul_mul, one_mul] at h
    exact h
  have hd : 3 ≤ Module.finrank K (Index (r + 1) → K) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨x, hx, hvx, hwx⟩ :=
    CFSGTypeAProjectivePointRoots.exists_nonzero_joint_kernel (pairingDual (r + 1) v)
      (pairingDual (r + 1) w) hd
  change pairing (r + 1) v x = 0 at hvx
  change pairing (r + 1) w x = 0 at hwx
  have hV : (V.val : Mat K (r + 1)) *ᵥ x = x := by
    change ((actualNaturalRootElement r hr v a).val : Mat K (r + 1)) *ᵥ x = x
    rw [actualNaturalRootElement_apply, transvection_apply, hvx, mul_zero, zero_smul, add_zero]
  have hW : (W.val : Mat K (r + 1)) *ᵥ x = x := by
    change ((actualNaturalRootElement r hr w b).val : Mat K (r + 1)) *ᵥ x = x
    rw [actualNaturalRootElement_apply, transvection_apply, hwx, mul_zero, zero_smul, add_zero]
  have hs := congrArg (fun M : Mat K (r + 1) => M *ᵥ x) hm
  change (V.val : Mat K (r + 1)) *ᵥ x = (c • (W.val : Mat K (r + 1))) *ᵥ x at hs
  rw [Matrix.smul_mulVec, hV, hW] at hs
  have hc1 : c = 1 := smul_left_injective K hx (by simpa only [one_smul] using hs.symm)
  apply Subtype.ext
  apply Units.ext
  simpa only [hc1, one_smul] using hm

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
