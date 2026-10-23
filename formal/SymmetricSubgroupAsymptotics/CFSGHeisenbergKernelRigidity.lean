import Mathlib.Tactic.Group
import SymmetricSubgroupAsymptotics.CFSGHeisenbergSymplecticQuotient

/-! Every nontrivial normal subgroup of the explicit Heisenberg group
meets its actual centre. Thus an actual homomorphism faithful on the
central root parameter is already faithful on all coordinates. This
avoids imposing a matrix-chart faithfulness hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergKernelRigidity
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSymplecticQuotient
variable {K G:Type*}[Field K][Group G]{m:ℕ}

theorem injective_of_central (f:Element K m→*G)
    (hc:Function.Injective (f.comp (central (K:=K) (m:=m)))) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hfg:f g=1 := hg
  have hzero (w:(Fin m→K)×(Fin m→K)) : pairing (g.a,g.b) w=0 := by
    let h:Element K m := ⟨w.1,w.2,0⟩
    have he : f (central (Multiplicative.ofAdd (pairing (g.a,g.b) w)))=1 := by
      rw [←commutator_eq_pairing g h,map_mul,map_mul,map_mul,map_inv,map_inv,hfg]
      group
    have hz : Multiplicative.ofAdd (pairing (g.a,g.b) w)=1 :=
      hc (he.trans (map_one (f.comp central)).symm)
    exact congrArg Multiplicative.toAdd hz
  have hv:(g.a,g.b)=(0,0) := by
    by_contra hv
    obtain ⟨w,hw⟩ := pairing_full (g.a,g.b) hv 1
    exact one_ne_zero (hw.symm.trans (hzero w))
  have hgker:g∈(projection (K:=K) (m:=m)).ker := (mem_projection_ker g).mpr (Prod.mk.inj hv)
  let z:Multiplicative K := (kernelChart (K:=K) (m:=m)).symm ⟨g,hgker⟩
  have hz:central z=g := congrArg Subtype.val
    ((kernelChart (K:=K) (m:=m)).apply_symm_apply ⟨g,hgker⟩)
  have hcz:(f.comp central) z=(f.comp central) 1 := by
    change f (central z)=f (central 1)
    rw [hz,hfg,map_one,map_one]
  have hz1:z=1 := hc hcz
  change g=1
  exact hz.symm.trans ((congrArg central hz1).trans (map_one central))

end SymmetricSubgroupAsymptotics.CFSGHeisenbergKernelRigidity
