import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel

/-! Affine orbit domination with the SAME actual linear part. For each
group element an affine fixed-point set is empty or is explicitly
equivalent, by translation, to the linear fixed subgroup. Burnside then
gives the actual orbit-card inequality. No split extension, vector-space
structure, character theorem or orbit domination premise is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AffineTorsorOrbitDomination

variable {G X V : Type*} [Group G] [AddCommGroup V]
    [MulAction G X] [DistribMulAction G V]
    (e:X≃V) (t:G→V) (h:∀(g:G)(x:X),e (g•x)=t g+g•e x)

def fixedByTranslate (g:G) (x₀:MulAction.fixedBy X g) :
    MulAction.fixedBy X g≃MulAction.fixedBy V g where
  toFun x := ⟨e x.val-e x₀.val,by
    change g•(e x.val-e x₀.val)=e x.val-e x₀.val
    calc
      g•(e x.val-e x₀.val)=g•e x.val-g•e x₀.val := smul_sub _ _ _
      _=(t g+g•e x.val)-(t g+g•e x₀.val) := by abel
      _=e x.val-e x₀.val := by
        rw [←h g x.val,←h g x₀.val,x.property,x₀.property]⟩
  invFun v := ⟨e.symm (e x₀.val+v.val),by
    have hv : g•v.val=v.val := v.property
    apply e.injective
    rw [h]
    simp only [e.apply_symm_apply,smul_add,hv]
    rw [←add_assoc,←h g x₀.val,x₀.property]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    change e (e.symm (e x₀.val+(e x.val-e x₀.val)))=e x.val
    rw [e.apply_symm_apply]
    abel
  right_inv v := by
    apply Subtype.ext
    change e (e.symm (e x₀.val+v.val))-e x₀.val=v.val
    rw [e.apply_symm_apply]
    abel

include e t h in
theorem fixedBy_card_le (g:G) :
    Nat.card (MulAction.fixedBy X g)≤Nat.card (MulAction.fixedBy V g) := by
  by_cases hx : ∃x:X,g•x=x
  · obtain ⟨x,hx⟩ := hx
    exact (Nat.card_congr (fixedByTranslate e t h g ⟨x,hx⟩)).le
  · letI : IsEmpty (MulAction.fixedBy X g) := ⟨fun x=>hx ⟨x.val,x.property⟩⟩
    have hz : Nat.card (MulAction.fixedBy X g)=0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz]
    exact Nat.zero_le _

include e t h in
theorem orbit_card_le [Finite G] [Finite X] [Finite V] :
    Nat.card (MulAction.orbitRel.Quotient G X)≤Nat.card (MulAction.orbitRel.Quotient G V) := by
  letI : Fintype G := Fintype.ofFinite _
  have hX : (∑g:G,Nat.card (MulAction.fixedBy X g))=
      Nat.card (MulAction.orbitRel.Quotient G X)*Nat.card G := by
    rw [←Nat.card_sigma,
      Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup G X),Nat.card_prod]
  have hV : (∑g:G,Nat.card (MulAction.fixedBy V g))=
      Nat.card (MulAction.orbitRel.Quotient G V)*Nat.card G := by
    rw [←Nat.card_sigma,
      Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup G V),Nat.card_prod]
  have hsum : (∑g:G,Nat.card (MulAction.fixedBy X g))≤
      ∑g:G,Nat.card (MulAction.fixedBy V g) :=
    Finset.sum_le_sum (fun (g:G) _=>fixedBy_card_le e t h g)
  rw [hX,hV] at hsum
  exact Nat.le_of_mul_le_mul_right hsum (Nat.card_pos (α:=G))

end SymmetricSubgroupAsymptotics.AffineTorsorOrbitDomination
