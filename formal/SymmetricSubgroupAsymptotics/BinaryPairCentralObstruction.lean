import SymmetricSubgroupAsymptotics.BinaryPairCentralKernel
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-! Sparse affine obstructions exclude central quotient classes over a
specified nontrivial top element. The constant term is the commutator of
an actual original section lift; the variable term is the complete
original kernel action. No split extension is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X ι : Type} {w a d : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

private theorem bits_mul (x y : F.top.ker) : F.bits (x*y)=F.bits x+F.bits y :=
  congrArg Multiplicative.toAdd (F.bitsHom.map_mul x y)
private theorem bits_inv (x : F.top.ker) : F.bits x⁻¹= -F.bits x :=
  congrArg Multiplicative.toAdd (F.bitsHom.map_inv x)

/-- A checked functional kills every possible kernel adjustment but
detects the section commutator. Thus no element above that section top
can become central modulo the exact original coordinate normal. -/
theorem central_quotient_obstruction
    (A : Subrepresentation F.coordinateTopAction)
    (C : BinaryCoordinateSpace w a) (hA : A.toSubmodule=C.space)
    (K : BinaryCoordinateSpace w d) (hK : F.kernelSpace=K.space)
    (generators : ι → U) (s : U) (commutators : ι → F.top.ker)
    (hcomm : ∀ j,(commutators j:U)=s⁻¹*(generators j*s*(generators j)⁻¹))
    (R : (ι → Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hzero : ∀ i,R (binaryCoordinate_generatorDefects F.coordinateTopAction
      (fun j => F.top.rangeRestrict (generators j)) C (K.inclusion (Pi.single i 1)))=0)
    (hconstant : R (fun j => C.defect (F.bits (commutators j)))≠0)
    (u : U) (htop : F.top u=F.top s)
    (hu : QuotientGroup.mk' (F.coordinateSubgroup A.toSubmodule) u∈
      Subgroup.center (U ⧸ F.coordinateSubgroup A.toSubmodule)) : False := by
  let k : F.top.ker := ⟨s⁻¹*u,by
    change F.top (s⁻¹*u)=1
    rw [map_mul,map_inv,htop,inv_mul_cancel]⟩
  have hu_eq : u=s*(k:U) := by simp only [k,mul_inv_cancel_left]
  let L := binaryCoordinate_generatorDefects F.coordinateTopAction
    (fun j => F.top.rangeRestrict (generators j)) C
  have hz : K.space≤(R.comp L).ker := K.le_of_basis_mem _ hzero
  have hkv : F.bits k∈K.space := hK ▸
    (show F.bits k∈F.kernelSpace from ⟨Additive.ofMul k,rfl⟩)
  have hr : R (L (F.bits k))=0 := hz hkv
  have hm (j : ι) :
      F.bits (k⁻¹*commutators j*MulAut.conjNormal (generators j) k)∈C.space := by
    rw [← hA]
    apply (F.kernel_mem_coordinateSubgroup A.toSubmodule _).mp
    have he : ((k⁻¹*commutators j*MulAut.conjNormal (generators j) k : F.top.ker):U)=
        u⁻¹*(generators j*u*(generators j)⁻¹) := by
      change (k:U)⁻¹*(commutators j:U)*
        (generators j*(k:U)*(generators j)⁻¹)=_
      rw [hcomm,hu_eq]
      group
    rw [he]
    exact ((binaryPair_quotient_center_iff (F.coordinateSubgroup A.toSubmodule)
      (fun x : U => x) (by simp) u).mp hu) (generators j)
  have hb (j : ι) :
      F.bits (k⁻¹*commutators j*MulAut.conjNormal (generators j) k)=
        F.bits (commutators j)+
          (F.coordinateTopAction (F.top.rangeRestrict (generators j)) (F.bits k)-F.bits k) := by
    rw [F.bits_mul,F.bits_mul,F.bits_inv,← F.coordinateTopAction_bits]
    abel
  have he : (fun j => C.defect (F.bits (commutators j)))+L (F.bits k)=0 := by
    funext j
    change C.defect (F.bits (commutators j))+
      C.defect (F.coordinateTopAction (F.top.rangeRestrict (generators j)) (F.bits k)-F.bits k)=0
    rw [← map_add,← hb j]
    exact (C.defect_eq_zero_iff _).mpr (hm j)
  have hh := congrArg R he
  rw [map_add,map_zero,hr,add_zero] at hh
  exact hconstant hh

end SymmetricSubgroupAsymptotics.BinaryPairFrame
