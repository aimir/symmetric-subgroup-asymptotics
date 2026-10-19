import SymmetricSubgroupAsymptotics.CliffordHomogeneousRestrictionInput
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation

/-! The original correlated elementary module embeds in its actual full
coordinate representation after local compression. The intertwining
identity is the literal wreath conjugation formula, not a Clifford input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CliffordHomogeneousRestriction
open PermutationalWreathProduct

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]
  (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

omit [Finite D'] in
private theorem localRepresentation_phi (d : S.D) (v : C.V) :
    (localRepresentation S phi hphi C).ρ (phi d) v=
      C.quotientRepresentation.ρ (QuotientGroup.mk' phi.ker d) v := by
  have he : (localQuotientEquiv S phi hphi).symm (phi d)=QuotientGroup.mk' phi.ker d := by
    apply (localQuotientEquiv S phi hphi).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change C.quotientRepresentation.ρ ((localQuotientEquiv S phi hphi).symm (phi d)) v=_
  rw [he]

omit [Finite D'] in
private theorem coordinate_conjugate (a : S.A) (n : elementaryKernel S phi) (i : I) :
    ((ActualWreathAffineCapacity.E S phi C).equiv (MulAut.conjNormal a n)).toAdd.val i=
      (localRepresentation S phi hphi C).ρ (phi ((S.rho a).left i))
        (((ActualWreathAffineCapacity.E S phi C).equiv n).toAdd.val
          ((S.rho a).right⁻¹ • i)) := by
  let k := Compression.kernelCoordinate S.rho phi ((S.rho a).right⁻¹ • i) n
  change (C.equiv (Compression.kernelCoordinate S.rho phi i (MulAut.conjNormal a n))).toAdd=
    (localRepresentation S phi hphi C).ρ (phi ((S.rho a).left i)) (C.equiv k).toAdd
  rw [localRepresentation_phi,ElementaryMinimalNormalChart.quotientRepresentation_apply]
  apply congrArg Multiplicative.toAdd
  apply congrArg C.equiv
  apply Subtype.ext
  change (S.rho (a*n.val*a⁻¹)).left i=
    (S.rho a).left i*(S.rho n.val).left ((S.rho a).right⁻¹ • i)*((S.rho a).left i)⁻¹
  rw [map_mul,map_mul,map_inv]
  have hn : (S.rho n.val).right=1 :=
    ((mem_mapBase_ker_iff phi (S.rho n.val)).mp n.property).1
  simp only [mul_left,mul_right,inv_left,Pi.mul_apply,Pi.inv_apply,hn,mul_one,
    smul_inv_smul]

abbrev coordinateEnvelope : Representation (ZMod C.p) (quotientGroup S phi) (I → C.V) :=
  (functionRepresentation (localRepresentation S phi hphi C).ρ).comp
    (Compression.quotientEmbedding S.rho phi)

/-- The original elementary representation with its scalar field made explicit. -/
abbrev elementaryCoordinateRepresentation : Representation (ZMod C.p) (quotientGroup S phi)
    (Compression.ElementarySubmodule (p := C.p) S.rho phi C.equiv.symm) :=
  (ActualWreathAffineCapacity.E S phi C).quotientRepresentation.ρ

def elementaryCoordinateEmbedding : Representation.IntertwiningMap
    (elementaryCoordinateRepresentation S phi C)
    (coordinateEnvelope S phi hphi C) where
  toLinearMap := (Compression.ElementarySubmodule (p := C.p) S.rho phi C.equiv.symm).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (elementaryKernel S phi) g
    let E := ActualWreathAffineCapacity.E S phi C
    let n : elementaryKernel S phi := E.equiv.symm (Multiplicative.ofAdd v)
    have hv : (E.equiv n).toAdd=v := congrArg Multiplicative.toAdd (E.equiv.apply_symm_apply _)
    rw [←hv]
    change (E.quotientRepresentation.ρ (QuotientGroup.mk' (elementaryKernel S phi) a)
      (E.equiv n).toAdd).val =
        (coordinateEnvelope S phi hphi C) (QuotientGroup.mk' (elementaryKernel S phi) a)
          (E.equiv n).toAdd.val
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    funext i
    exact coordinate_conjugate S phi hphi C a n i

omit [Finite D'] in
theorem elementaryCoordinateEmbedding_injective :
    Function.Injective (elementaryCoordinateEmbedding S phi hphi C) :=
  Subtype.val_injective

end SymmetricSubgroupAsymptotics.CliffordHomogeneousRestriction
