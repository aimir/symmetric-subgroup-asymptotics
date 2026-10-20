import SymmetricSubgroupAsymptotics.SixPairNestedTopFrames
import Mathlib.Algebra.CharP.Two

/-! Two literal binary block layers force fourth powers to vanish in the
ACTUAL original coarse kernel. This includes nonsplit and noncommutative
kernels; an elementary-kernel assumption is neither made nor inferred. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairThreePairKernelExponent

variable {X I J : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J (ZMod 2))

private theorem pair_kernel_square {Y K : Type} {H : Subgroup (Equiv.Perm Y)}
    (B : BinaryPairFrame H K) (k : B.top.ker) : (k : H)^2=1 := by
  have he : k^2=1 := by
    apply B.bitsHom_injective
    rw [map_pow,map_one,pow_two]
    apply Multiplicative.toAdd.injective
    change B.bits k+B.bits k=0
    funext i
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val he

/-- Squaring an actual coarse-kernel element lands in the original pair
kernel, whose second square is the identity. -/
theorem fourth_power (g : (SixPairNestedTopFrames.nestedFrame F E).top.ker) : g^4=1 := by
  let B : BinaryPairFrame F.top.range J :=
    { frame := E.frame,top := E.top,intertwine := E.intertwine }
  let k : B.top.ker := ⟨F.top.rangeRestrict g.val,g.property⟩
  have ht : (F.top g.val)^2=1 :=
    congrArg (fun z : F.top.range => z.val) (pair_kernel_square B k)
  have hg : g.val^2∈F.top.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow,ht]
  have hh := pair_kernel_square F ⟨g.val^2,hg⟩
  apply Subtype.ext
  change g.val^4=1
  rw [show (4 : ℕ)=2*2 by norm_num,pow_mul]
  exact hh

/-- Binaryity follows directly from the proved fourth-power relation. -/
theorem kernel_binary : IsPGroup 2 (SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  intro g
  refine ⟨2,?_⟩
  norm_num only [show (2 : ℕ)^2=4 by norm_num]
  exact fourth_power F E g

end SymmetricSubgroupAsymptotics.SixPairThreePairKernelExponent
