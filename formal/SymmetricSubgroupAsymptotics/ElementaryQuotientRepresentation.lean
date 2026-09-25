import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The original action on an elementary quotient is constructed from
the actual epimorphism and invariant kernel. No split extension or
preexisting action on the quotient is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {p : ℕ} [Fact p.Prime] {H R V : Type} [Group H] [Group R]
variable [AddCommGroup V] [Module (ZMod p) V]
variable (α : H→*MulAut R) (φ : R→*Multiplicative V) (hφ : Function.Surjective φ)
variable (hker : ∀ (h:H) (r:R),φ r=1→φ (α h r)=1)

def elementaryQuotientActionHom (h:H) : Multiplicative V→*Multiplicative V :=
  (QuotientGroup.lift φ.ker (φ.comp (α h).toMonoidHom) (fun r hr=>hker h r hr)).comp
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom

theorem elementaryQuotientActionHom_apply (h:H) (r:R) :
    elementaryQuotientActionHom α φ hφ hker h (φ r)=φ (α h r) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  change QuotientGroup.lift φ.ker (φ.comp (α h).toMonoidHom) (fun r hr=>hker h r hr)
    (e.symm (e (QuotientGroup.mk r)))=_
  rw [e.symm_apply_apply]
  rfl

def elementaryQuotientActionLinear (h:H) : V→ₗ[ZMod p]V :=
  (show V→+V from {
    toFun v := (elementaryQuotientActionHom α φ hφ hker h (Multiplicative.ofAdd v)).toAdd
    map_zero' := congrArg Multiplicative.toAdd (map_one _)
    map_add' v w := congrArg Multiplicative.toAdd
      (map_mul (elementaryQuotientActionHom α φ hφ hker h)
        (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }).toZModLinearMap p

theorem elementaryQuotientActionLinear_apply (h:H) (r:R) :
    elementaryQuotientActionLinear (p:=p) α φ hφ hker h (φ r).toAdd=(φ (α h r)).toAdd :=
  congrArg Multiplicative.toAdd (elementaryQuotientActionHom_apply α φ hφ hker h r)

def elementaryQuotientRepresentation : Representation (ZMod p) H V where
  toFun := elementaryQuotientActionLinear (p:=p) α φ hφ hker
  map_one' := by
    apply LinearMap.ext
    intro v
    obtain ⟨r,hr⟩ := hφ (Multiplicative.ofAdd v)
    have hv : v=(φ r).toAdd := (congrArg Multiplicative.toAdd hr).symm
    rw [hv,elementaryQuotientActionLinear_apply,map_one]
    rfl
  map_mul' h k := by
    apply LinearMap.ext
    intro v
    obtain ⟨r,hr⟩ := hφ (Multiplicative.ofAdd v)
    have hv : v=(φ r).toAdd := (congrArg Multiplicative.toAdd hr).symm
    change elementaryQuotientActionLinear (p:=p) α φ hφ hker (h*k) v=
      elementaryQuotientActionLinear (p:=p) α φ hφ hker h
        (elementaryQuotientActionLinear (p:=p) α φ hφ hker k v)
    rw [hv,elementaryQuotientActionLinear_apply,elementaryQuotientActionLinear_apply,
      elementaryQuotientActionLinear_apply,map_mul,MulAut.mul_apply]

theorem elementaryQuotientRepresentation_equivariant (h:H) (r:R) :
    (φ (α h r)).toAdd=elementaryQuotientRepresentation (p:=p) α φ hφ hker h (φ r).toAdd :=
  (elementaryQuotientActionLinear_apply (p:=p) α φ hφ hker h r).symm

end SymmetricSubgroupAsymptotics
