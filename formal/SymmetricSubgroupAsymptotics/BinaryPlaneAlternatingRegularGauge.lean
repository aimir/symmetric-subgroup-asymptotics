import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerKleinLift

/-! Coordinates transported by a genuine regular subgroup of the actual
linear image. Only the supplied regular subgroup is untwisted. No section
of an affine extension, or label for its full block normalizer, is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRegularGauge
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible

open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem regular_apply (r s : R) : regular r • label s = label (r*s) := by
  change label (r * label.symm (label s)) = label (r*s)
  rw [label.symm_apply_apply]

variable (C : Subgroup Frame) (lift : R →* C)
  (htop : ∀ r, (lift r : Frame).right = regular r)

/-- The map from the base plane to a block is the actual local transport
of the unique regular lift carrying the base block to that block. -/
def transport (r : R) : Linear :=
  (lift r : Frame).left (label r)

include htop in
theorem transport_mul (r s : R) :
    transport C lift (r*s) =
      (lift r : Frame).left (label (r*s)) *
        transport C lift s := by
  have hi : (regular r)⁻¹ • label (r*s) = label s := by
    rw [← regular_apply r s, inv_smul_smul]
  have hm := congrArg
    (fun g : C => (g : Frame).left (label (r*s)))
    (lift.map_mul r s)
  simpa only [transport, Subgroup.coe_mul,
    PermutationalWreathProduct.mul_left, Pi.mul_apply, htop r, hi] using hm

/-- The exact binary-linear label, retaining all actual local maps. -/
def gauge : (Fin 4 → Plane) ≃ₗ[ZMod 2] (R → Plane) where
  toFun v r := (transport C lift r).symm (v (label r))
  invFun v i := transport C lift (label.symm i) (v (label.symm i))
  left_inv v := by
    funext i
    simp only [Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  right_inv v := by
    funext r
    simp only [Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  map_add' v w := by
    funext r
    exact map_add _ _ _
  map_smul' a v := by
    funext r
    exact (transport C lift r).symm.map_smul a (v (label r))

include htop in
/-- Along the genuine regular lift the transported action is literally
the regular permutation action. This says nothing about other elements. -/
theorem gauge_lift (r : R) (v : Fin 4 → Plane) (s : R) :
    gauge C lift
      (BinaryPlaneCyclicWreathUniform.representation C (lift r) v) s =
      gauge C lift v (r⁻¹*s) := by
  have hi : (regular r)⁻¹ • label s = label (r⁻¹*s) := by
    rw [← map_inv]
    exact regular_apply r⁻¹ s
  have ht := transport_mul C lift htop r (r⁻¹*s)
  rw [mul_inv_cancel_left] at ht
  apply (transport C lift s).injective
  change (transport C lift s)
    ((transport C lift s).symm
      ((lift r : Frame).left (label s)
        (v ((lift r : Frame).right⁻¹ • label s)))) =
    (transport C lift s)
      ((transport C lift (r⁻¹*s)).symm (v (label (r⁻¹*s))))
  rw [LinearEquiv.apply_symm_apply, htop r, hi, ht]
  change _ = (lift r : Frame).left (label s)
    ((transport C lift (r⁻¹*s))
      ((transport C lift (r⁻¹*s)).symm (v (label (r⁻¹*s)))))
  rw [LinearEquiv.apply_symm_apply]

include htop in
/-- A top-trivial element commuting with the chosen regular subgroup
becomes the same local linear operator on every block. In the rank-one
case this binds the diagonal cubic action to the actual odd kernel. -/
theorem gauge_commuting (k : C)
    (hk : (k : Frame).right = 1)
    (hc : ∀ r, Commute (lift r) k)
    (v : Fin 4 → Plane) (r : R) :
    gauge C lift
      (BinaryPlaneCyclicWreathUniform.representation C k v) r =
      (k : Frame).left (label 1)
        (gauge C lift v r) := by
  have hi : (regular r)⁻¹ • label r = label 1 := by
    rw [← map_inv]
    simpa only [inv_mul_cancel] using regular_apply r⁻¹ r
  have hm := congrArg
    (fun g : C => (g : Frame).left (label r)) (hc r).eq
  have ht : transport C lift r *
      (k : Frame).left (label 1) =
      (k : Frame).left (label r) *
        transport C lift r := by
    simpa only [transport, Subgroup.coe_mul,
      PermutationalWreathProduct.mul_left, Pi.mul_apply, htop r, hk,
      inv_one, one_smul, hi] using hm
  apply (transport C lift r).injective
  change (transport C lift r)
    ((transport C lift r).symm
      ((k : Frame).left (label r)
        (v ((k : Frame).right⁻¹ • label r)))) =
    ((transport C lift r) *
      (k : Frame).left (label 1))
      ((transport C lift r).symm (v (label r)))
  rw [LinearEquiv.apply_symm_apply, hk, inv_one, one_smul, ht]
  change _ = (k : Frame).left (label r)
    ((transport C lift r)
      ((transport C lift r).symm (v (label r))))
  rw [LinearEquiv.apply_symm_apply]

/-- The lift and coordinate chart are constructed in the actual linear
image. Every actual odd-kernel element has its exact constant operator;
no scalar structure or full-normalizer gauge is assumed. -/
theorem exists_actual_gauge
    (e : BinaryPlaneWreathActualOddKernel.oddKernel C ≃*
      BinaryPlaneAlternatingKernelPartition.Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ l : R →* C, Function.Injective l ∧
      (∀ r, (l r : Frame).right=regular r) ∧
      (∀ r (v : Fin 4 → Plane) s,
        gauge C l (BinaryPlaneCyclicWreathUniform.representation C (l r) v) s =
          gauge C l v (r⁻¹*s)) ∧
      ∀ (o : BinaryPlaneWreathActualOddKernel.oddKernel C)
        (v : Fin 4 → Plane) r,
        gauge C l (BinaryPlaneCyclicWreathUniform.representation C (o : C) v) r =
          ((o : C) : Frame).left (label 1) (gauge C l v r) := by
  obtain ⟨l,hl,ht,hc⟩ :=
    BinaryPlaneAlternatingCentralizerKleinLift.exists_regular_hom C e heven
  refine ⟨l,hl,ht,?_,?_⟩
  · exact gauge_lift C l ht
  · intro o v r
    exact gauge_commuting C l ht (o : C)
      (BinaryPlaneWreathActualOddKernel.top_one C o) (fun s => hc s o) v r

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRegularGauge
