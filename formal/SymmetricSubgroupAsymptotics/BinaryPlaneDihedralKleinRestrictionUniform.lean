import SymmetricSubgroupAsymptotics.DihedralEightRegularKleinBlockModel
import SymmetricSubgroupAsymptotics.BinaryPlaneKleinUniform

/-! Restrict an actual D8 quartet image to the preimage of its regular V4
subgroup. The actual odd kernel is retained, so the subgroup is nonbinary.
Its uniform bound then enlarges to the original acting group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneDihedralKleinRestrictionUniform
open BinaryPlaneWreathIrreducible BinaryPlanePermutationAffineEquiv
open DihedralEightRegularKleinBlockModel
open BinaryPlaneWreathActualOddKernel
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq
abbrev Small := W (R := R) (I := R)
abbrev Large := W (R := Q) (I := R)

def inclusion : Small →* Large where
  toFun g := ⟨g.left,regular g.right⟩
  map_one' := by apply PermutationalWreathProduct.ext <;> simp
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      change g.left i*h.left (g.right⁻¹*i)=
        g.left i*h.left ((regular g.right)⁻¹ • i)
      rw [← map_inv,regular_smul]
    · exact regular.map_mul _ _

theorem inclusion_injective : Function.Injective inclusion := by
  intro g h he
  apply PermutationalWreathProduct.ext
  · exact congrArg (fun z : Large => z.left) he
  · exact regular_injective (congrArg (fun z : Large => z.right) he)

variable (C : Subgroup Large)
abbrev restricted := C.comap inclusion

def restrictedMap : restricted C →* C :=
  (inclusion.comp (restricted C).subtype).codRestrict C (fun g => g.property)

theorem restricted_blocks (honto : Function.Surjective
    ((PermutationalWreathProduct.rightHom : Large →* Q).comp C.subtype)) :
    Function.Surjective
      ((PermutationalWreathProduct.rightHom : Small →* R).comp (restricted C).subtype) := by
  intro r
  obtain ⟨g,hg⟩ := honto (regular r)
  let w : Small := ⟨(g : Large).left,r⟩
  have he : inclusion w=(g : Large) := by
    apply PermutationalWreathProduct.ext
    · rfl
    · exact hg.symm
  exact ⟨⟨w,by change inclusion w∈C; rw [he]; exact g.property⟩,rfl⟩

theorem restricted_nonbinary (hC : ¬ IsPGroup 2 C) : ¬ IsPGroup 2 (restricted C) := by
  have hO : oddKernel C≠⊥ := oddKernel_ne_bot C binary hC
  letI : Nontrivial (oddKernel C) := (oddKernel C).nontrivial_iff_ne_bot.mpr hO
  obtain ⟨o,ho⟩ := exists_ne (1 : oddKernel C)
  let w : Small := ⟨((o : C) : Large).left,1⟩
  have he : inclusion w=((o : C) : Large) := by
    apply PermutationalWreathProduct.ext
    · rfl
    · simpa only [map_one] using (top_one C o).symm
  let z : restricted C := ⟨w,by change inclusion w∈C; rw [he]; exact (o : C).property⟩
  have hz : z^3=1 := by
    apply Subtype.ext
    apply inclusion_injective
    change inclusion (w^3)=inclusion 1
    rw [map_pow,map_one,he]
    exact congrArg (fun t : oddKernel C => ((t : C) : Large)) (cube_eq_one C o)
  have hn : z≠1 := by
    intro h
    apply ho
    apply Subtype.ext
    apply Subtype.ext
    have hv := congrArg (fun x : restricted C => inclusion (x : Small)) h
    change inclusion w=inclusion 1 at hv
    simpa only [he,map_one] using hv
  intro hp
  apply hn
  apply (hp.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using hz

/-- Uniform bound for the full original D8-image action, including all
proper correlated odd and binary translation submodules. -/
theorem uniform (hC : ¬ IsPGroup 2 C)
    (honto : Function.Surjective
      ((PermutationalWreathProduct.rightHom : Large →* Q).comp C.subtype)) :
    UniformSubrepresentationGeneratorBound
      (BinaryPlaneCyclicWreathUniform.representation C) 2 := by
  have hk := BinaryPlaneKleinUniform.uniform (restricted C)
    (restricted_nonbinary C hC) (restricted_blocks C honto)
  have he : BinaryPlaneKleinUniform.representation (restricted C)=
      (BinaryPlaneCyclicWreathUniform.representation C).comp (restrictedMap C) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    funext i
    change (g : Small).left i (v ((g : Small).right⁻¹*i))=
      (g : Small).left i (v ((regular (g : Small).right)⁻¹ • i))
    rw [← map_inv,regular_smul]
  rw [he] at hk
  exact UniformSubrepresentationGeneratorBound.of_comp
    (BinaryPlaneCyclicWreathUniform.representation C) (restrictedMap C) hk

end SymmetricSubgroupAsymptotics.BinaryPlaneDihedralKleinRestrictionUniform
