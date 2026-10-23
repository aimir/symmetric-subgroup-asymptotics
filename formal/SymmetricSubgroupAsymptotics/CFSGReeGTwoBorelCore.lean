import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCardinalitySylow
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentre
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOppositionTorus
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The actual fixed Borel has trivial normal core. A normal subgroup
inside B is first forced into the actual torus by opposition, then its
commutators with U vanish by U-intersection-T, and faithful torus action
on the positive centre kills it. No simplicity or perfectness is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoBorelCore
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOriginalOpposition CFSGReeGTwoOppositionTorus
open CFSGReeGTwoFixedRankOneGeometry CFSGReeGTwoFixedCardinalitySylow
open CFSGReeGTwoPositiveDerived CFSGReeGTwoPositiveCentre

theorem fixedTorus_mem_borel (m : ℕ) (t : (Field m)ˣ) :
    fixedTorusHom m t∈borelGroup m := by
  refine ⟨(⟨1,t⟩:BorelSource m),?_⟩
  simp only [borelHom_apply,Subgroup.coe_one,one_mul]

theorem opposed_borel_mem_torus (m : ℕ) (g : originalModelFixed m)
    (hg : g∈borelGroup m)
    (hopp : fixedOpposition m*g*(fixedOpposition m)⁻¹∈borelGroup m) :
    g∈(fixedTorusHom m).range := by
  obtain ⟨x,rfl⟩ := hg
  let u := x.left.val
  let t := fixedTorusHom m x.right
  have hu : u∈fixedPositiveGroup m := x.left.property
  have he : borelHom m x=u*t := rfl
  have htu : fixedOpposition m*t⁻¹*(fixedOpposition m)⁻¹∈borelGroup m := by
    dsimp only [t]
    rw [←map_inv,fixedOpposition_fixedTorus]
    exact fixedTorus_mem_borel m _
  have huc : fixedOpposition m*u*(fixedOpposition m)⁻¹∈borelGroup m := by
    have hh := (borelGroup m).mul_mem hopp htu
    have hid : (fixedOpposition m*borelHom m x*(fixedOpposition m)⁻¹)*
        (fixedOpposition m*t⁻¹*(fixedOpposition m)⁻¹)=
        fixedOpposition m*u*(fixedOpposition m)⁻¹ := by rw [he];group
    rwa [hid] at hh
  have hu1 := fixed_opposed_positive_intersection m u hu huc
  refine ⟨x.right,?_⟩
  rw [he,hu1,one_mul]

private theorem normal_le_torus (m : ℕ) (C : Subgroup (originalModelFixed m))
    [hC : C.Normal] (hCB : C≤borelGroup m) : C≤(fixedTorusHom m).range := by
  intro g hg
  exact opposed_borel_mem_torus m g (hCB hg)
    (hCB (hC.conj_mem g hg (fixedOpposition m)))

theorem normal_le_borel_eq_bot (m : ℕ) (C : Subgroup (originalModelFixed m))
    [hC : C.Normal] (hCB : C≤borelGroup m) : C=⊥ := by
  have hCT := normal_le_torus m C hCB
  apply bot_unique
  intro g hg
  obtain ⟨t,ht⟩ := hCT hg
  have hcomm (u : originalModelFixed m) (hu : u∈fixedPositiveGroup m) :
      g*u*g⁻¹=u := by
    let d := g*u*g⁻¹*u⁻¹
    have hdC : d∈C := by
      have hh := C.mul_mem hg (hC.conj_mem g⁻¹ (C.inv_mem hg) u)
      simpa only [d,mul_assoc] using hh
    have hdU : d∈fixedPositiveGroup m :=
      (fixedPositiveGroup m).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (borelGroup_le_normalizer m (hCB hg)) u).mp hu)
        ((fixedPositiveGroup m).inv_mem hu)
    have hd : d∈fixedPositiveGroup m ⊓ (fixedTorusHom m).range := ⟨hdU,hCT hdC⟩
    rw [positive_inf_torus_eq_bot] at hd
    have hd1 : g*u*g⁻¹*u⁻¹=1 := hd
    exact mul_inv_eq_one.mp hd1
  have hc : fixedPositiveTorusAut m t (centralHom m (Multiplicative.ofAdd (1:Field m)))=
      centralHom m (Multiplicative.ofAdd (1:Field m)) := by
    apply Subtype.ext
    rw [fixedPositiveTorusAut_val,ht]
    exact hcomm _ (centralHom m (Multiplicative.ofAdd (1:Field m))).property
  rw [torusAction_centralHom,one_mul] at hc
  have htval : (t:Field m)=1 := congrArg Multiplicative.toAdd (centralHom_injective m hc)
  have ht1 : t=1 := Units.ext htval
  apply Subgroup.mem_bot.mpr
  exact ht.symm.trans (by rw [ht1,map_one])

theorem fixed_borel_normalCore (m : ℕ) : (borelGroup m).normalCore=⊥ :=
  normal_le_borel_eq_bot m _ (borelGroup m).normalCore_le

def fixedCosetAction (m : ℕ) : originalModelFixed m→*
    Equiv.Perm (originalModelFixed m⧸borelGroup m) :=
  MulAction.toPermHom _ _

theorem fixedCosetAction_injective (m : ℕ) : Function.Injective (fixedCosetAction m) := by
  apply (fixedCosetAction m).ker_eq_bot_iff.mp
  change (MulAction.toPermHom (originalModelFixed m) (originalModelFixed m⧸borelGroup m)).ker=⊥
  rw [←Subgroup.normalCore_eq_ker,fixed_borel_normalCore]

end SymmetricSubgroupAsymptotics.CFSGReeGTwoBorelCore
