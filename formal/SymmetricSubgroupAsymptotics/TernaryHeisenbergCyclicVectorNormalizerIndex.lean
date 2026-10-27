import SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorExt
import SymmetricSubgroupAsymptotics.CFSGHeisenbergTransitiveActionIndex
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Tactic.FinCases

/-! One actual normalizing element suffices when its compatible vector
quotient has transitive powers on the eight nonzero ternary vectors.
The finite compatible subgroup retains the original ambient word and both
actual automorphisms; neither its order nor injectivity of the covering
semidirect evaluation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryHeisenbergCyclicVectorNormalizerIndex
open CFSGHeisenbergCoordinateGroup
private abbrev P := ZMod 3
private abbrev Heis := Element P 1
private abbrev V := P × P
private abbrev MV := Multiplicative V

private def projection : Heis →* MV where
  toFun h := Multiplicative.ofAdd (h.a 0,h.b 0)
  map_one' := rfl
  map_mul' _ _ := rfl

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

private def quotientHom (f : Heis →* G) : compatible f →* MulAut MV where
  toFun t := t.val.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem card_ge_twentySeven_of_central_moved [Finite G]
    {X : Type*} [Finite X] [MulAction G X]
    (f : Heis →* G) (u : G) (α : MulAut Heis) (σ : MulAut MV)
    (hu : ∀ h, u*f h*u⁻¹=f (α h))
    (hcompat : ∀ h, Multiplicative.ofAdd ((α h).a 0,(α h).b 0)=
      σ (Multiplicative.ofAdd (h.a 0,h.b 0)))
    (htrans : ∀ v w : V, v≠0 → w≠0 →
      ∃ k : ℕ, (σ^k) (Multiplicative.ofAdd v)=Multiplicative.ofAdd w)
    (x : X) (hmove : f TernaryHeisenbergGeneratorExt.third • x≠x) :
    27 ≤ Nat.card X := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Finite (MulAut Heis) := Finite.of_injective
    (fun a : MulAut Heis => (a : Heis → Heis)) DFunLike.coe_injective
  letI : Finite (MulAut MV) := Finite.of_injective
    (fun a : MulAut MV => (a : MV → MV)) DFunLike.coe_injective
  letI : MulAction (compatible f) V := scalarAction f
  letI : MulAction (compatible f) ((Fin 1 → P) × (Fin 1 → P)) := vectorAction f
  let U : compatible f := ⟨(u,(α,σ)),⟨fun h => (hu h).symm,hcompat⟩⟩
  have hz (t : compatible f) : t • (0 : (Fin 1 → P) × (Fin 1 → P))=0 := by
    apply vectorEquiv.injective
    change (t.val.2.2 (1 : MV)).toAdd=0
    rw [map_one]
    rfl
  have ht (z w : (Fin 1 → P) × (Fin 1 → P)) (hz : z≠0) (hw : w≠0) :
      ∃ t : compatible f, t • z=w := by
    have hz' : vectorEquiv z≠0 := fun he => hz (vectorEquiv.injective he)
    have hw' : vectorEquiv w≠0 := fun he => hw (vectorEquiv.injective he)
    obtain ⟨k,hk⟩ := htrans (vectorEquiv z) (vectorEquiv w) hz' hw'
    refine ⟨U^k,vectorEquiv.injective ?_⟩
    change ((quotientHom f (U^k)) (Multiplicative.ofAdd (vectorEquiv z))).toAdd=vectorEquiv w
    rw [map_pow]
    exact congrArg Multiplicative.toAdd hk
  have hφ (t : compatible f) (h : Heis) :
      ((actionHom f t h).a,(actionHom f t h).b)=t • (h.a,h.b) := by
    apply vectorEquiv.injective
    exact congrArg Multiplicative.toAdd (t.property.2 h)
  let c : Multiplicative P := Multiplicative.ofAdd 1
  letI : MulAction (Heis ⋊[actionHom f] compatible f) X :=
    MulAction.compHom _ (totalHom f)
  let M := MulAction.stabilizer (Heis ⋊[actionHom f] compatible f) x
  have hmove' : (SemidirectProduct.inl (central (m := 1) c) :
      Heis ⋊[actionHom f] compatible f) • x≠x := by
    change (f (central (m := 1) c)*1) • x≠x
    simpa only [mul_one] using hmove
  have hcentre : ¬(central (K := P) (m := 1)).range ≤ M.comap SemidirectProduct.inl := by
    intro hh
    exact hmove' (hh ⟨c,rfl⟩)
  have hb : 27 ≤ M.index := by
    simpa only [Nat.card_zmod,Nat.reduceMul,Nat.reducePow] using
      CFSGHeisenbergTransitiveActionIndex.prime_mul_field_power_le_index
        (actionHom f) 3 hz ht hφ M hcentre
  have ho : M.index=Nat.card (MulAction.orbit (Heis ⋊[actionHom f] compatible f) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ x)).symm
  have hcard := Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (Heis ⋊[actionHom f] compatible f) x => y.val) Subtype.val_injective
  exact hb.trans (ho.trans_le hcard)

theorem proper_index_ge_twentySeven [Finite G] [IsSimpleGroup G]
    (f : Heis →* G) (u : G) (α : MulAut Heis) (σ : MulAut MV)
    (hu : ∀ h, u*f h*u⁻¹=f (α h))
    (hcompat : ∀ h, Multiplicative.ofAdd ((α h).a 0,(α h).b 0)=
      σ (Multiplicative.ofAdd (h.a 0,h.b 0)))
    (htrans : ∀ v w : V, v≠0 → w≠0 →
      ∃ k : ℕ, (σ^k) (Multiplicative.ofAdd v)=Multiplicative.ofAdd w)
    (hne : f TernaryHeisenbergGeneratorExt.third≠1)
    (J : Subgroup G) (hJ : J≠⊤) : 27 ≤ J.index := by
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one J hJ _ hne
  exact (card_ge_twentySeven_of_central_moved f u α σ hu hcompat htrans x hx).trans_eq
    J.index_eq_card.symm

end SymmetricSubgroupAsymptotics.TernaryHeisenbergCyclicVectorNormalizerIndex
