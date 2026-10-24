import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! One genuine opposed-subgroup peel. A smaller residual subgroup is
intersected with the next conjugate of the original positive group.
An available inversion block gives a bijective product, provided it is
contained in the current residual. No normality or group order formula
is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling
variable {G : Type*} [Group G]

def inversionPart (U V : Subgroup G) (w : G) : Subgroup G :=
  U ⊓ V.comap (MulAut.conj w).toMonoidHom

def remainderPart (U R : Subgroup G) (w : G) : Subgroup G :=
  U ⊓ R.map (MulAut.conj w).toMonoidHom

private theorem inverse_conjugate_mem (R : Subgroup G) (w r : G)
    (hr : r ∈ R.map (MulAut.conj w).toMonoidHom) : w⁻¹*r*w ∈ R := by
  obtain ⟨x,hx,he⟩ := hr
  change w*x*w⁻¹=r at he
  have h : w⁻¹*r*w=x := by rw [←he]; group
  rw [h]
  exact hx

def peelProduct (U V R : Subgroup G) (w : G)
    (hBR : inversionPart U V w ≤ R) :
    remainderPart U R w × inversionPart U V w → R := fun p =>
  ⟨w⁻¹*p.1.val*w*p.2.val,
    R.mul_mem (inverse_conjugate_mem R w p.1.val p.1.property.2) (hBR p.2.property)⟩

theorem peelProduct_injective (U V R : Subgroup G) (w : G)
    (hBR : inversionPart U V w ≤ R) (hdis : Disjoint U V) :
    Function.Injective (peelProduct U V R w hBR) := by
  intro a b he
  have hv := congrArg (fun r : R => r.val) he
  change w⁻¹*a.1.val*w*a.2.val = w⁻¹*b.1.val*w*b.2.val at hv
  have hc : a.1.val*(w*a.2.val*w⁻¹) = b.1.val*(w*b.2.val*w⁻¹) := by
    calc
      _=w*(w⁻¹*a.1.val*w*a.2.val)*w⁻¹ := by group
      _=w*(w⁻¹*b.1.val*w*b.2.val)*w⁻¹ := congrArg (fun r : G => w*r*w⁻¹) hv
      _=_ := by group
  let pa : U × V := (⟨a.1.val,a.1.property.1⟩,⟨w*a.2.val*w⁻¹,a.2.property.2⟩)
  let pb : U × V := (⟨b.1.val,b.1.property.1⟩,⟨w*b.2.val*w⁻¹,b.2.property.2⟩)
  have hp : pa=pb := Subgroup.mul_injective_of_disjoint hdis hc
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun p : U × V => p.1.val) hp)
  · apply Subtype.ext
    apply (MulAut.conj w).injective
    exact congrArg (fun p : U × V => p.2.val) hp

theorem peelProduct_bijective (U V R : Subgroup G) (w : G)
    (hRU : R ≤ U) (hBR : inversionPart U V w ≤ R) (hdis : Disjoint U V)
    (hfactor : ∀ x ∈ U, ∃ p ∈ U, ∃ b ∈ inversionPart U V w,
      x=p*b ∧ w*p*w⁻¹∈U) :
    Function.Bijective (peelProduct U V R w hBR) := by
  refine ⟨peelProduct_injective U V R w hBR hdis,?_⟩
  intro x
  obtain ⟨p,hp,b,hb,hprod,hconj⟩ := hfactor x.val (hRU x.property)
  have hpR : p∈R := by
    have h := R.mul_mem x.property (R.inv_mem (hBR hb))
    simpa only [hprod,mul_inv_cancel_right] using h
  let r : remainderPart U R w := ⟨w*p*w⁻¹,⟨hconj,⟨p,hpR,rfl⟩⟩⟩
  refine ⟨(r,⟨b,hb⟩),?_⟩
  apply Subtype.ext
  change w⁻¹*(w*p*w⁻¹)*w*b=x.val
  rw [hprod]
  group

theorem card_eq_remainder_mul_inversion [Finite G] (U V R : Subgroup G) (w : G)
    (hRU : R ≤ U) (hBR : inversionPart U V w ≤ R) (hdis : Disjoint U V)
    (hfactor : ∀ x ∈ U, ∃ p ∈ U, ∃ b ∈ inversionPart U V w,
      x=p*b ∧ w*p*w⁻¹∈U) :
    Nat.card R = Nat.card (remainderPart U R w) * Nat.card (inversionPart U V w) := by
  have h := Nat.card_congr (Equiv.ofBijective (peelProduct U V R w hBR)
    (peelProduct_bijective U V R w hRU hBR hdis hfactor))
  rw [Nat.card_prod] at h
  exact h.symm

end SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling
