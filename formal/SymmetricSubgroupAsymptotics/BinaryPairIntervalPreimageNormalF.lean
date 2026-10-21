import SymmetricSubgroupAsymptotics.PGroupInvariantSubrepresentationInterval
import SymmetricSubgroupAsymptotics.BinaryPairConstantFlipPreimageCard
import SymmetricSubgroupAsymptotics.BinaryPairAffineProperFCardPacket
import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds

/-! One actual invariant interval A<S installs proper normal F in the
SAME original quotient. The full lower layer remains present; arbitrary
original affine offsets are retained except for one proved zero-class
central constant flip. No finite model, augmentation condition or capacity
callback appears in the result. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance intervalPreimageNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin (w+w))) (E : BinaryPairFrame F.top.range (Fin w))
    [MulAction.IsPretransitive U X]

theorem interval_preimage_normalF_packet
    (hU : IsPGroup 2 U) (i : Fin w)
    (A S : Subrepresentation (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin w)))
    (hK : F.kernelSpace=S.toSubmodule.comap E.pairSum)
    (hAS : A.toSubmodule<S.toSubmodule)
    (hsmall : 2*Module.finrank (ZMod 2) A.toSubmodule<w)
    (z : E.top.ker) (hzbits : E.bits z=(fun _ => 1))
    (hzcentral : z.val∈Subgroup.center F.top.range) (hzero : F.affineClass z.val=0)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (haxis : F.ambientAxis N=A.toSubmodule.map E.pairConstant) :
    ∃ D : Subgroup (U ⧸ N),D.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤(w : ℝ)+(w : ℝ) ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog D≤(w : ℝ) := by
  letI : MulAction.IsPretransitive F.top.range (Fin (w+w)) := F.top_pretransitive
  letI : MulAction.IsPretransitive E.top.range (Fin w) := E.top_pretransitive
  have hH := F.top_isPGroup hU
  obtain ⟨T,hAT,hTS,hTdisp⟩ := pGroup_exists_trivial_subrepresentation_interval
    (E.top_isPGroup hH) _ A S hAS
  let B := T.toSubmodule.comap E.pairSum
  let C := A.toSubmodule.comap E.pairSum
  have hB : B≤F.kernelSpace := by
    rw [hK]
    exact Submodule.comap_mono hTS
  have hC : C≤F.kernelSpace := by
    rw [hK]
    exact Submodule.comap_mono hAS.le
  have hCB : C≤B := Submodule.comap_mono hAT.le
  have hCstable : ∀ r v,v∈C → F.ambientAffineLinearAction r v∈C := by
    intro r v hv
    exact E.pairSum_preimage_stable A r v hv
  have hBdisp : ∀ r v,v∈B → F.ambientAffineLinearAction r v-v∈C := by
    intro r v hv
    exact E.pairSum_preimage_interval_displacement A T hTdisp r v hv
  have hzdisp : ∀ v,F.ambientAffineLinearAction z.val v-v∈C := by
    intro v
    change permutationFunctionRepresentation (ZMod 2) F.top.range (Fin (w+w)) z.val v-v∈C
    rw [E.constant_flip_displacement z hzbits]
    change E.pairSum (E.pairConstant (E.pairSum v))∈A.toSubmodule
    rw [E.pairSum_pairConstant]
    exact A.toSubmodule.zero_mem
  have hAC : F.ambientAxis N≤C := by
    rw [haxis]
    rintro _ ⟨a,ha,rfl⟩
    change E.pairSum (E.pairConstant a)∈A.toSubmodule
    rw [E.pairSum_pairConstant]
    exact A.toSubmodule.zero_mem
  have hAcard : Nat.card A.toSubmodule=Nat.card N := by
    have hc := F.axis_card_eq_kernel_intersection N
    rw [inf_eq_right.mpr hN,haxis,E.pairConstant_image_card] at hc
    exact hc
  have hcomm : Nat.card C≤Nat.card N*2^w := by
    change Nat.card (A.toSubmodule.comap E.pairSum)≤_
    rw [E.pairSum_preimage_card,hAcard]
    exact le_of_eq (Nat.mul_comm _ _)
  have hfixed : Nat.card {v : Fin (w+w) → ZMod 2 // v∈F.kernelSpace ∧
      F.coordinateTopAction z.val v-v∈F.ambientAxis N}=Nat.card N*2^w := by
    rw [hK,haxis]
    change Nat.card {v : Fin (w+w) → ZMod 2 // v∈S.toSubmodule.comap E.pairSum ∧
      permutationFunctionRepresentation (ZMod 2) F.top.range (Fin (w+w)) z.val v-v∈
        A.toSubmodule.map E.pairConstant}=Nat.card N*2^w
    rw [E.constant_flip_fixed_preimage_card A.toSubmodule S.toSubmodule hAS.le z hzbits,hAcard]
    exact Nat.mul_comm _ _
  have htop : Nat.card {t : F.top.range // ∀ v,v∈B →
      F.coordinateTopAction t v-v∈F.ambientAxis N}≤1 := by
    rw [haxis]
    exact E.interval_preimage_stabilizer_card_le_one hH i A T hsmall (not_le_of_gt hAT)
  exact F.affine_properF_unit_packet_of_card_bounds B C z.val hB hC hCB hzcentral hzero
    hCstable hBdisp hzdisp N hN hAC w w hcomm (by
      calc
        _ ≤ Nat.card {v : Fin (w+w) → ZMod 2 // v∈F.kernelSpace ∧
            F.coordinateTopAction z.val v-v∈F.ambientAxis N}*1 := Nat.mul_le_mul_left _ htop
        _ = Nat.card N*2^w := by rw [Nat.mul_one,hfixed])

end SymmetricSubgroupAsymptotics.BinaryPairFrame
