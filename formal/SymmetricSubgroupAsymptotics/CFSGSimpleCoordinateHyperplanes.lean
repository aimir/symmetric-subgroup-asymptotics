import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisPermutation
import Mathlib.Algebra.BigOperators.Pi

/-! Permuting actual additive coordinate axes also permutes their
complementary coordinate kernels. No scalar linearity is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateHyperplanes
open CFSGSimpleCoordinateAxes
variable {J K : Type*} [Fintype J] [DecidableEq J] [AddCommGroup K]

def additiveMap (F : MulAut (Multiplicative (J→K))) : (J→K)→+(J→K) where
  toFun c := (F (Multiplicative.ofAdd c)).toAdd
  map_zero' := by
    change F 1=1
    exact map_one F
  map_add' c d := by
    change F (Multiplicative.ofAdd c*Multiplicative.ofAdd d)=
      F (Multiplicative.ofAdd c)*F (Multiplicative.ofAdd d)
    exact map_mul F _ _

theorem coordinate_zero_forward (F : MulAut (Multiplicative (J→K))) (σ : Equiv.Perm J)
    (hF : ∀j : J,(axis (K:=K) j).map F.toMonoidHom=axis (K:=K) (σ j))
    (i : J) (c : Multiplicative (J→K)) (hc : c.toAdd i=0) : (F c).toAdd (σ i)=0 := by
  classical
  have he : additiveMap F c.toAdd=∑j : J,additiveMap F (Pi.single j (c.toAdd j) : J→K) := by
    rw [←map_sum,Finset.univ_sum_single]
  change (additiveMap F c.toAdd) (σ i)=0
  rw [he,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : j=i
  · subst j
    rw [hc,Pi.single_zero,map_zero]
    rfl
  · have hm : F (Multiplicative.ofAdd (Pi.single j (c.toAdd j) : J→K))∈axis (K:=K) (σ j) := by
      rw [←hF j]
      exact ⟨_,single_mem_axis j (c.toAdd j),rfl⟩
    exact hm (σ i) (fun h=>hji (σ.injective h).symm)

theorem coordinate_zero_iff (F : MulAut (Multiplicative (J→K))) (σ : Equiv.Perm J)
    (hF : ∀j : J,(axis (K:=K) j).map F.toMonoidHom=axis (K:=K) (σ j))
    (i : J) (c : Multiplicative (J→K)) : (F c).toAdd (σ i)=0↔c.toAdd i=0 := by
  have hInv : ∀j : J,(axis (K:=K) j).map F.symm.toMonoidHom=axis (K:=K) (σ.symm j) := by
    intro j
    apply Subgroup.map_injective (f := F.toMonoidHom) F.injective
    have hcomp : F.toMonoidHom.comp F.symm.toMonoidHom=MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact F.apply_symm_apply x
    rw [Subgroup.map_map,hcomp,Subgroup.map_id,hF,Equiv.apply_symm_apply]
  constructor
  · intro hc
    have hh := coordinate_zero_forward F.symm σ.symm hInv (σ i) (F c) hc
    simpa only [MulEquiv.symm_apply_apply,Equiv.symm_apply_apply] using hh
  · exact coordinate_zero_forward F σ hF i c

end SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateHyperplanes
