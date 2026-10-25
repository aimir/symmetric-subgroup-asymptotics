import SymmetricSubgroupAsymptotics.CFSGHeisenbergTransitiveActionIndex
import SymmetricSubgroupAsymptotics.TernaryPlaneRotationShearTransitivity
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Tactic.FinCases

/-! A faithful ACTUAL Heisenberg27 image with two actual normalizing
rotation/shear elements pays proper index27. A finite compatible
normalizer records simultaneously the ambient element, its actual
Heisenberg automorphism, and its quotient automorphism. Its semidirect
product only COVERS the source; no splitting or normalizer order is
asserted. All stabilizer factors belong to the SAME pulled-back subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryHeisenbergCompatibleNormalizerIndex
open CFSGHeisenbergCoordinateGroup
private abbrev P := ZMod 3
private abbrev Heis := Element P 1
private abbrev V := P × P
private abbrev MV := Multiplicative V

private def projection : Heis →* MV where
  toFun h := Multiplicative.ofAdd (h.a 0,h.b 0)
  map_one' := rfl
  map_mul' _ _ := rfl

private def rotationVector : MulAut MV where
  toFun v := Multiplicative.ofAdd (-v.toAdd.2,v.toAdd.1)
  invFun v := Multiplicative.ofAdd (v.toAdd.2,-v.toAdd.1)
  left_inv v := by apply Multiplicative.toAdd.injective; exact Prod.ext rfl (neg_neg _)
  right_inv v := by apply Multiplicative.toAdd.injective; exact Prod.ext (neg_neg _) rfl
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · change -(v.toAdd.2+w.toAdd.2)= -v.toAdd.2+ -w.toAdd.2
      ring
    · rfl

private def shearVector : MulAut MV where
  toFun v := Multiplicative.ofAdd (v.toAdd.1,v.toAdd.2+v.toAdd.1)
  invFun v := Multiplicative.ofAdd (v.toAdd.1,v.toAdd.2-v.toAdd.1)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · rfl
    · change (v.toAdd.2+v.toAdd.1)-v.toAdd.1=v.toAdd.2
      ring
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · rfl
    · change (v.toAdd.2-v.toAdd.1)+v.toAdd.1=v.toAdd.2
      ring
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · rfl
    · change (v.toAdd.2+w.toAdd.2)+(v.toAdd.1+w.toAdd.1)=
        (v.toAdd.2+v.toAdd.1)+(w.toAdd.2+w.toAdd.1)
      ring

variable {G : Type*} [Group G]

private def compatible (f : Heis →* G) : Subgroup (G × (MulAut Heis × MulAut MV)) where
  carrier := {t | (∀ h, f (t.2.1 h)=t.1*f h*t.1⁻¹) ∧
    (∀ h, projection (t.2.1 h)=t.2.2 (projection h))}
  one_mem' := by constructor <;> intro h <;> simp
  mul_mem' := by
    intro t u ht hu
    constructor
    · intro h
      change f (t.2.1 (u.2.1 h))=(t.1*u.1)*f h*(t.1*u.1)⁻¹
      rw [ht.1,hu.1]
      group
    · intro h
      change projection (t.2.1 (u.2.1 h))=t.2.2 (u.2.2 (projection h))
      rw [ht.2,hu.2]
  inv_mem' := by
    intro t ht
    constructor
    · intro h
      have he : f h=t.1*f ((t.2.1)⁻¹ h)*t.1⁻¹ := by
        simpa only [MulAut.apply_inv_self] using ht.1 ((t.2.1)⁻¹ h)
      change f ((t.2.1)⁻¹ h)=t.1⁻¹*f h*(t.1⁻¹)⁻¹
      rw [he]
      group
    · intro h
      have he : projection h=t.2.2 (projection ((t.2.1)⁻¹ h)) := by
        simpa only [MulAut.apply_inv_self] using ht.2 ((t.2.1)⁻¹ h)
      change projection ((t.2.1)⁻¹ h)=(t.2.2)⁻¹ (projection h)
      rw [he]
      exact ((t.2.2).symm_apply_apply _).symm

private def actionHom (f : Heis →* G) : compatible f →* MulAut Heis where
  toFun t := t.val.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[reducible] private def scalarAction (f : Heis →* G) : MulAction (compatible f) V where
  smul t v := (t.val.2.2 (Multiplicative.ofAdd v)).toAdd
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def vectorEquiv : ((Fin 1 → P) × (Fin 1 → P)) ≃ V where
  toFun v := (v.1 0,v.2 0)
  invFun v := (fun _ => v.1,fun _ => v.2)
  left_inv v := by
    apply Prod.ext
    · funext i; fin_cases i; rfl
    · funext i; fin_cases i; rfl
  right_inv _ := rfl

@[reducible] private def vectorAction (f : Heis →* G) :
    MulAction (compatible f) ((Fin 1 → P) × (Fin 1 → P)) := by
  letI := scalarAction f
  exact
    { smul := fun t v => vectorEquiv.symm (t • vectorEquiv v)
      one_smul := by
        intro v
        change vectorEquiv.symm ((1 : compatible f) • vectorEquiv v)=v
        rw [one_smul,Equiv.symm_apply_apply]
      mul_smul := by
        intro t u v
        change vectorEquiv.symm ((t*u) • vectorEquiv v)=
          vectorEquiv.symm (t • vectorEquiv (vectorEquiv.symm (u • vectorEquiv v)))
        rw [Equiv.apply_symm_apply,mul_smul] }

private def totalHom (f : Heis →* G) : Heis ⋊[actionHom f] compatible f →* G where
  toFun t := f t.left*t.right.val.1
  map_one' := by simp
  map_mul' t u := by
    change f (t.left*actionHom f t.right u.left)*(t.right.val.1*u.right.val.1)=
      (f t.left*t.right.val.1)*(f u.left*u.right.val.1)
    rw [map_mul]
    change f t.left*f (t.right.val.2.1 u.left)*(t.right.val.1*u.right.val.1)=
      (f t.left*t.right.val.1)*(f u.left*u.right.val.1)
    rw [t.right.property.1]
    group

/-- Only actual finite-group words and a faithful Heisenberg homomorphism
are premises. No order, splitting or capacity bound is supplied. -/
theorem proper_index_ge_twentySeven [Finite G] [IsSimpleGroup G]
    (f : Heis →* G) (hf : Function.Injective f)
    (u v : G) (α β : MulAut Heis)
    (hu : ∀ h, u*f h*u⁻¹=f (α h)) (hv : ∀ h, v*f h*v⁻¹=f (β h))
    (hα : ∀ h, ((α h).a 0,(α h).b 0)=(-h.b 0,h.a 0))
    (hβ : ∀ h, ((β h).a 0,(β h).b 0)=(h.a 0,h.b 0+h.a 0))
    (H : Subgroup G) (hH : H≠⊤) : 27 ≤ H.index := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Finite (MulAut Heis) := Finite.of_injective
    (fun a : MulAut Heis => (a : Heis → Heis)) DFunLike.coe_injective
  letI : Finite (MulAut MV) := Finite.of_injective
    (fun a : MulAut MV => (a : MV → MV)) DFunLike.coe_injective
  letI : MulAction (compatible f) V := scalarAction f
  letI : MulAction (compatible f) ((Fin 1 → P) × (Fin 1 → P)) := vectorAction f
  let U : compatible f := ⟨(u,(α,rotationVector)),
    ⟨fun h => (hu h).symm,fun h => congrArg Multiplicative.ofAdd (hα h)⟩⟩
  let D : compatible f := ⟨(v,(β,shearVector)),
    ⟨fun h => (hv h).symm,fun h => congrArg Multiplicative.ofAdd (hβ h)⟩⟩
  have hU (w : V) : U • w=(-w.2,w.1) := rfl
  have hD (w : V) : D • w=(w.1,w.2+w.1) := rfl
  have hz (t : compatible f) : t • (0 : (Fin 1 → P) × (Fin 1 → P))=0 := by
    apply vectorEquiv.injective
    change (t.val.2.2 (1:MV)).toAdd=0
    rw [map_one]
    rfl
  have ht (z w : (Fin 1 → P) × (Fin 1 → P)) (hz : z≠0) (hw : w≠0) :
      ∃ t : compatible f, t • z=w := by
    have hz' : vectorEquiv z≠0 := fun he => hz (vectorEquiv.injective he)
    have hw' : vectorEquiv w≠0 := fun he => hw (vectorEquiv.injective he)
    obtain ⟨t,he⟩ := TernaryPlaneRotationShearTransitivity.transitive_nonzero
      U D hU hD (vectorEquiv z) (vectorEquiv w) hz' hw'
    exact ⟨t,vectorEquiv.injective he⟩
  have hφ (t : compatible f) (h : Heis) :
      ((actionHom f t h).a,(actionHom f t h).b)=t • (h.a,h.b) := by
    apply vectorEquiv.injective
    exact congrArg Multiplicative.toAdd (t.property.2 h)
  let c : Multiplicative P := Multiplicative.ofAdd 1
  have hc : central (m := 1) c≠1 := by
    intro he
    have hh := central_injective (he.trans (map_one central).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd hh)
  have hfc : f (central (m := 1) c)≠1 := by
    intro he
    exact hc (hf (he.trans f.map_one.symm))
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hfc
  letI : MulAction (Heis ⋊[actionHom f] compatible f) (G ⧸ H) :=
    MulAction.compHom _ (totalHom f)
  let M := MulAction.stabilizer (Heis ⋊[actionHom f] compatible f) x
  have hmove : (SemidirectProduct.inl (central (m := 1) c) :
      Heis ⋊[actionHom f] compatible f) • x≠x := by
    change (f (central (m := 1) c)*1) • x≠x
    simpa only [mul_one] using hx
  have hcentre : ¬(central (K := P) (m := 1)).range ≤ M.comap SemidirectProduct.inl := by
    intro hh
    exact hmove (hh ⟨c,rfl⟩)
  have hb : 27 ≤ M.index := by
    simpa only [Nat.card_zmod,Nat.reduceMul,Nat.reducePow] using
      CFSGHeisenbergTransitiveActionIndex.prime_mul_field_power_le_index
        (actionHom f) 3 hz ht hφ M hcentre
  have ho : M.index=Nat.card (MulAction.orbit (Heis ⋊[actionHom f] compatible f) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ x)).symm
  have hcard := Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (Heis ⋊[actionHom f] compatible f) x => y.val) Subtype.val_injective
  exact hb.trans ((ho.trans_le hcard).trans_eq (H.index_eq_card).symm)

end SymmetricSubgroupAsymptotics.TernaryHeisenbergCompatibleNormalizerIndex
