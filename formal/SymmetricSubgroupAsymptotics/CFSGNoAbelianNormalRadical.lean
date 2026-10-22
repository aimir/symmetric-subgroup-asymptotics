import SymmetricSubgroupAsymptotics.CFSGSolubleRadical
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Absence of abelian normal subgroups eliminates every soluble normal
subgroup. The proof uses the literal derived series of that subgroup and
its actual characteristic images in the original ambient group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.CFSGNoAbelianNormalRadical

variable {G : Type} [Group G]

theorem soluble_normal_eq_bot
    (hNo : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → N=⊥)
    (C : Subgroup G) [C.Normal] [IsSolvable C] : C=⊥ := by
  have hstep : ∀ n : ℕ, derivedSeries C n=⊥ → C=⊥ := by
    intro n
    induction n with
    | zero =>
        intro hz
        by_contra hc
        letI : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hc
        exact top_ne_bot (by simpa only [derivedSeries_zero] using hz)
    | succ n ih =>
        intro hz
        let D := derivedSeries C n
        have hcomm : ⁅D,D⁆=⊥ := hz
        letI : IsMulCommutative D := ⟨⟨fun x y => by
          apply Subtype.ext
          have hh := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) x.property
          exact ((Subgroup.mem_centralizer_iff.mp hh) y y.property).symm⟩⟩
        let E := D.map C.subtype
        let e : D ≃* E := D.equivMapOfInjective C.subtype C.subtype_injective
        haveI : IsMulCommutative E := ⟨⟨fun x y => by
          obtain ⟨a,rfl⟩ := e.surjective x
          obtain ⟨b,rfl⟩ := e.surjective y
          rw [←map_mul,←map_mul,mul_comm a b]⟩⟩
        have hE : E=⊥ := hNo E inferInstance inferInstance
        have hD : D=⊥ := (Subgroup.map_eq_bot_iff_of_injective D C.subtype_injective).mp hE
        exact ih hD
  obtain ⟨n,hn⟩ := (isSolvable_def C).mp inferInstance
  exact hstep n hn

theorem radical_eq_bot [Finite G]
    (hNo : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → N=⊥) :
    CFSGReduction.solubleRadical G=⊥ := soluble_normal_eq_bot hNo _

end SymmetricSubgroupAsymptotics.CFSGNoAbelianNormalRadical
