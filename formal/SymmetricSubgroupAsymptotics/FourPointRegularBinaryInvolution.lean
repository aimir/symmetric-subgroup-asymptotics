import SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge
import Mathlib.GroupTheory.GroupAction.Basic

/-! On four points, a fixed-point-free involution belongs to every
regular elementary binary subgroup. This identifies a translation from
its actual action, rather than from an abstract order match. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.FourPointRegularBinaryInvolution
open BinaryFourBlockAugmentation

local instance : DecidableEq Local := BinaryFourLocalCubicPointGauge.pointDecidableEq
local instance : Fintype (Equiv.Perm Local) := Equiv.instFintype
local instance : DecidableEq (Equiv.Perm Local) := Fintype.decidableEqEquivFintype

private theorem free_involutions_commute (c t : Equiv.Perm Local)
    (hc : c^2 = 1) (ht : t^2 = 1)
    (hcf : ∀ v, c v ≠ v) (htf : ∀ v, t v ≠ v) : c*t=t*c := by
  have finite : ∀ c t : Equiv.Perm Local,
      c^2=1 → t^2=1 → (∀ v,c v≠v) → (∀ v,t v≠v) →
      ∀ v, c (t v)=t (c v) := by decide +kernel
  apply Equiv.ext
  exact finite c t hc ht hcf htf

theorem mem_regular {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]
    (V : Subgroup G) [IsMulCommutative V]
    (b : X ≃ Local) (x : X)
    (hregular : ∀ y : X, ∃! v : V, v • x = y)
    (hfree : ∀ v : V, ∀ y : X, v • y = y → v=1)
    (hV2 : ∀ v : V, v^2=1)
    (g : G) (hg2 : g^2=1) (hgf : ∀ y : X, g • y ≠ y) : g ∈ V := by
  let f : G →* Equiv.Perm Local :=
    b.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hf : Function.Injective f :=
    b.permCongrHom.injective.comp MulAction.toPerm_injective
  have hcomm (u : V) : g*(u:G)=(u:G)*g := by
    by_cases hu : u=1
    · simp [hu]
    apply hf
    simp only [map_mul]
    apply free_involutions_commute
    · rw [←map_pow,hg2,map_one]
    · have h : (u:G)^2=1 := congrArg Subtype.val (hV2 u)
      rw [←map_pow,h,map_one]
    · intro v h
      have he := congrArg b.symm h
      change b.symm (b (g • b.symm v)) = b.symm v at he
      rw [b.symm_apply_apply] at he
      exact hgf (b.symm v) he
    · intro v h
      have he := congrArg b.symm h
      change b.symm (b ((u:G) • b.symm v)) = b.symm v at he
      rw [b.symm_apply_apply] at he
      exact hu (hfree u (b.symm v) he)
  obtain ⟨v,hv,hvu⟩ := hregular (g • x)
  change (v:G) • x = g • x at hv
  have hgv : g=(v:G) := by
    apply (show Function.Injective (MulAction.toPermHom G X) from MulAction.toPerm_injective)
    apply Equiv.ext
    intro y
    obtain ⟨u,hu,huu⟩ := hregular y
    change (u:G) • x = y at hu
    change g • y = (v:G) • y
    have hcu : (u:G)*(v:G)=(v:G)*(u:G) :=
      congrArg Subtype.val (mul_comm u v)
    calc
      g • y = g • ((u:G) • x) := by rw [hu]
      _ = (u:G) • (g • x) := by rw [←mul_smul,hcomm u,mul_smul]
      _ = (u:G) • ((v:G) • x) := by rw [hv]
      _ = (v:G) • ((u:G) • x) := by rw [←mul_smul,hcu,mul_smul]
      _ = (v:G) • y := by rw [hu]

  rw [hgv]
  exact v.2

end SymmetricSubgroupAsymptotics.FourPointRegularBinaryInvolution
