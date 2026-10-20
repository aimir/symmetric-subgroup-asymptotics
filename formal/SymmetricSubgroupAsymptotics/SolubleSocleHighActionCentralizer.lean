import SymmetricSubgroupAsymptotics.FiniteIsotypicHighAction
import SymmetricSubgroupAsymptotics.SolubleSocleModuleCard

/-! Identity action on an actual integral socle submodule is exactly
membership in its original ambient centralizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

theorem scalar_identity_iff_mem_centralizer
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (S : Submodule ℤ[G] (representation N).asModule) (g : G) :
    (∀ x : (representation N).asModule, x ∈ S → MonoidAlgebra.of ℤ G g • x=x) ↔
      g ∈ Subgroup.centralizer (submoduleGroup N S : Set G) := by
  constructor
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    let n : N := ⟨s,submoduleGroup_le N S hs⟩
    let x : (representation N).asModule := Additive.ofMul n
    have hx : x ∈ S := (mem_submoduleGroup N S n).mp hs
    have he := h x hx
    change MonoidAlgebra.single g (1 : ℤ) • x=x at he
    rw [Representation.single_smul,one_smul] at he
    have hconj := congrArg (fun y : Additive N => (y.toMul : G)) he
    change g*s*g⁻¹=s at hconj
    have hm := congrArg (fun y : G => y*g) hconj
    have hcomm : g*s=s*g := by
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm
    exact hcomm.symm
  · intro h x hx
    have hs : (x.toMul : G) ∈ submoduleGroup N S :=
      (mem_submoduleGroup N S x.toMul).mpr hx
    have hc : (x.toMul : G)*g=g*(x.toMul : G) :=
      Subgroup.mem_centralizer_iff.mp h _ hs
    change MonoidAlgebra.single g (1 : ℤ) • x=x
    rw [Representation.single_smul,one_smul]
    apply Additive.toMul.injective
    apply Subtype.ext
    change g*(x.toMul : G)*g⁻¹=(x.toMul : G)
    rw [←hc,mul_inv_cancel_right]

theorem highAction_ker_eq_centralizer
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (D : FiniteIsotypicRowData ℤ[G] (representation N).asModule) (t : ℕ) :
    (D.highAction t).ker=Subgroup.centralizer (submoduleGroup N (D.highModule t) : Set G) := by
  ext g
  rw [D.highAction_ker_identity,scalar_identity_iff_mem_centralizer]

end SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
