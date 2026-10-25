import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassBound

/-! Actual block-kernel coordinates in ONE original component. The
chosen transporters do not replace the kernel by a product. Full local
realization proves every image normal in the same original component. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualBlockCommonKernelCoordinates
open OriginalBlockClassBound ActualBlockWreathEmbedding

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)

theorem kernel_right_one (k : Kernel (A := A) (X := X)) :
    (embedding b hb x0 k.val).right = 1 :=
  Subtype.ext k.property

def kernelCoordinate (i : X) :
    Kernel (A := A) (X := X) →* originalBlockComponent b hb x0 where
  toFun k := (embedding b hb x0 k.val).left i
  map_one' := by simp only [Subgroup.coe_one,map_one,PermutationalWreathProduct.one_left,Pi.one_apply]
  map_mul' k l := by
    change (embedding b hb x0 (k.val * l.val)).left i =
      (embedding b hb x0 k.val).left i * (embedding b hb x0 l.val).left i
    rw [map_mul,PermutationalWreathProduct.mul_left,Pi.mul_apply,kernel_right_one b hb x0 k]
    simp only [inv_one,one_smul]

theorem kernelCoordinates_injective :
    Function.Injective (fun k => fun i => kernelCoordinate b hb x0 i k) := by
  intro k l he
  apply Subtype.ext
  apply embedding_injective b hb x0
  apply PermutationalWreathProduct.ext
  · exact funext (fun i => congrFun he i)
  · exact (kernel_right_one b hb x0 k).trans (kernel_right_one b hb x0 l).symm

theorem kernelCoordinate_range_normal (i : X) :
    (kernelCoordinate b hb x0 i).range.Normal := by
  constructor
  rintro _ ⟨k,rfl⟩ c
  obtain ⟨a,ha,hac⟩ := fullComponent b hb x0 i c
  let z : Kernel (A := A) (X := X) := MulAut.conjNormal a k
  refine ⟨z,?_⟩
  change (embedding b hb x0 (a * k.val * a⁻¹)).left i =
    c * (embedding b hb x0 k.val).left i * c⁻¹
  rw [map_mul,map_mul,map_inv,
    PermutationalWreathProduct.conj_left_of_fixed _ _ i ha (kernel_right_one b hb x0 k),hac]

theorem kernel_card_le_component_power [Finite A] [Finite Ω] [Finite X] :
    Nat.card (Kernel (A := A) (X := X)) ≤
      Nat.card (originalBlockComponent b hb x0) ^ Nat.card X := by
  have h := Nat.card_le_card_of_injective (fun k => fun i => kernelCoordinate b hb x0 i k)
    (kernelCoordinates_injective b hb x0)
  simpa only [Nat.card_fun] using h

end SymmetricSubgroupAsymptotics.ActualBlockCommonKernelCoordinates
