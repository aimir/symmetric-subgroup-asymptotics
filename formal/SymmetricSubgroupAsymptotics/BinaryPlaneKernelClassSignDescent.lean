import SymmetricSubgroupAsymptotics.CubicKernelConjugationSignRigidity
import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCubic

/-! Actual top-kernel signs are constant on each literal cubic-kernel
class. In the one-class case the entire actual top kernel embeds in one
native GL2(F2) coordinate. No A4/S4 top assumption, independent coordinate
choice, or external cubic action is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassSignDescent
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] (C : Subgroup (W (R := R) (I := I)))

private theorem toThree_local_ker (i : I) :
    (toThree.comp (localLinear C i)).ker = localKernel C i := by
  ext u
  change toThree (localLinear C i u) = 1 ↔ localLinear C i u = 1
  constructor
  · intro h
    exact toThree_injective (h.trans (map_one toThree).symm)
  · intro h
    rw [h,map_one]

theorem sign_eq_of_top_one_of_localKernel_eq (h : C)
    (ht : (h : W (R := R) (I := I)).right = 1) (i j : I)
    (hker : localKernel C i = localKernel C j)
    (hlocal : ∃ u : oddKernel C, localLinear C i u ≠ 1) :
    oddMarkerSign (toThree ((h : W (R := R) (I := I)).left i)) =
      oddMarkerSign (toThree ((h : W (R := R) (I := I)).left j)) := by
  have hne : ∃ u : oddKernel C, (toThree.comp (localLinear C i)) u ≠ 1 := by
    obtain ⟨u,hu⟩ := hlocal
    refine ⟨u,?_⟩
    intro he
    exact hu (toThree_injective (he.trans (map_one toThree).symm))
  refine CubicKernelConjugationSignRigidity.sign_eq_of_common_cubic_kernel
    (toThree.comp (localLinear C i)) (toThree.comp (localLinear C j))
    ((toThree_local_ker C i).trans (hker.trans (toThree_local_ker C j).symm))
    (fun u => by change toThree (localLinear C i u)^3 = 1; rw [←map_pow,local_cubic C i u,map_one])
    (fun u => by change toThree (localLinear C j u)^3 = 1; rw [←map_pow,local_cubic C j u,map_one])
    hne (MulAut.conjNormal h)
    (toThree ((h : W (R := R) (I := I)).left i))
    (toThree ((h : W (R := R) (I := I)).left j)) ?_ ?_
  · intro u
    have hh := localLinear_conjugate C h u i
    rw [ht,one_smul] at hh
    change toThree (localLinear C i ((MulAut.conjNormal h) u)) = _
    rw [hh,map_mul,map_mul,map_inv]
    rfl
  · intro u
    have hh := localLinear_conjugate C h u j
    rw [ht,one_smul] at hh
    change toThree (localLinear C j ((MulAut.conjNormal h) u)) = _
    rw [hh,map_mul,map_mul,map_inv]
    rfl

def topKernelLocal (i : I) : (PermutationalWreathProduct.rightHom.comp C.subtype).ker →* Linear where
  toFun u := ((u : C) : W (R := R) (I := I)).left i
  map_one' := rfl
  map_mul' u v := by
    have ht : ((u : C) : W (R := R) (I := I)).right = 1 := u.property
    change ((((u : C) : W (R := R) (I := I))*((v : C) : W (R := R) (I := I))).left i) = _
    rw [PermutationalWreathProduct.mul_left]
    simp only [Pi.mul_apply,ht,inv_one,one_smul]

theorem topKernelLocal_injective_of_single_class (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hlocal : ∃ u : oddKernel C, localLinear C i₀ u ≠ 1) :
    Function.Injective (topKernelLocal C i₀) := by
  apply (topKernelLocal C i₀).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx0 : ((x : C) : W (R := R) (I := I)).left i₀ = 1 := hx
  have hxt : ((x : C) : W (R := R) (I := I)).right = 1 := x.property
  have hsign (i : I) : oddMarkerSign (toThree (((x : C) : W (R := R) (I := I)).left i)) = 1 := by
    have hh := sign_eq_of_top_one_of_localKernel_eq C (x : C) hxt i₀ i (hsingle i).symm hlocal
    rw [hx0,map_one,map_one] at hh
    exact hh.symm
  have hmem : (x : C) ∈ oddKernel C := by
    change signProjection C (x : C) = 1
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      change (oddMarkerSign (toThree (((x : C) : W (R := R) (I := I)).left i))).toAdd = 0
      rw [hsign]
      rfl
    · exact hxt
  let o : oddKernel C := ⟨(x : C),hmem⟩
  have ho : o = 1 := BinaryPlaneSingleKernelCubic.localLinear_injective C i₀ hsingle i₀
    (by change ((x : C) : W (R := R) (I := I)).left i₀ = localLinear C i₀ 1; rw [hx0,map_one])
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact congrArg (fun u : oddKernel C => (u : C)) ho

end SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassSignDescent
