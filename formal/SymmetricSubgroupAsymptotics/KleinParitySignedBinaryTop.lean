import SymmetricSubgroupAsymptotics.FourBlockKleinSignBase
import SymmetricSubgroupAsymptotics.CyclicQuotientRelativeHeadTwo

/-! The signed regular Klein action with sign parity tied to the second
block bit. This literal group has order32 and center of order at most2. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.KleinParitySignedBinaryTop
open SemidirectProduct
open FourBlockKleinSignBase (Base first second)
abbrev Vector := Fin 4 → ZMod 2
abbrev E := FourBlockBinarySignSpaces.space (R := Base) false
abbrev Full := CyclicOrbitBinarySignNormalGenerators.Model E
abbrev Bit := Multiplicative (ZMod 2)
local instance : Finite Full := Finite.of_equiv
  (Multiplicative E.toSubmodule × Base) SemidirectProduct.equivProd.symm
local instance : DecidableEq Full := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩; exact SemidirectProduct.ext hl hr
    · intro he; exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)

def raw (v : Vector) (b : Base) : Full :=
  ⟨Multiplicative.ofAdd ⟨v,Submodule.mem_top⟩,b⟩

def parity : Full →* Bit where
  toFun g := Multiplicative.ofAdd ((∑ i, g.left.toAdd.val i)+g.right.2.toAdd)
  map_one' := by simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change (∑ i, (g.left.toAdd.val i+h.left.toAdd.val (g.right⁻¹ • i)))+
        (g.right.2.toAdd+h.right.2.toAdd)=
      ((∑ i,g.left.toAdd.val i)+g.right.2.toAdd)+
        ((∑ i,h.left.toAdd.val i)+h.right.2.toAdd)
    rw [Finset.sum_add_distrib]
    have hs : (∑ i, h.left.toAdd.val (g.right⁻¹ • i))=∑ i,h.left.toAdd.val i :=
      Equiv.sum_comp (MulAction.toPermHom Base (Fin 4) g.right⁻¹) h.left.toAdd.val
    rw [hs]
    ring

abbrev Group := parity.ker

def x : Full := raw 0 first
def y : Full := raw (Pi.single 1 1) second

theorem x_mem : x∈Group := by decide +kernel
theorem y_mem : y∈Group := by decide +kernel

def X : Group := ⟨x,x_mem⟩
def Y : Group := ⟨y,y_mem⟩

private def vectorEquiv : E.toSubmodule ≃ Vector where
  toFun v := v.val
  invFun v := ⟨v,Submodule.mem_top⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem full_card : Nat.card Full=64 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd : Full ≃ Multiplicative E.toSubmodule × Base),
    Nat.card_prod,Nat.card_congr Multiplicative.toAdd,Nat.card_congr vectorEquiv,
    Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num [Base,FourBlockKleinSignBase.Base,TernaryFourBlockKleinSocles.Complement,
    TernaryFourBlockKleinSocles.Bit,TernaryFourBlockMetacyclicModel.Bit,Nat.card_prod,
    Nat.card_eq_fintype_card]

theorem parity_surjective : Function.Surjective parity := by
  intro z
  refine ⟨raw (![z.toAdd,0,0,0]) 1,?_⟩
  have h : ∀ b : Bit, parity (raw (![b.toAdd,0,0,0]) 1)=b := by decide +kernel
  exact h z

theorem group_card : Nat.card Group=32 := by
  have hq : Nat.card (Full ⧸ Group)=2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective parity parity_surjective).toEquiv]
    norm_num [Bit,Nat.card_eq_fintype_card]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Group
  rw [full_card,hq] at h
  omega

theorem isPGroup : IsPGroup 2 Group := IsPGroup.of_card (n := 5) group_card

private theorem center_detector : ∀ (v : Vector) (b : Base),
    parity (raw v b)=1 → raw v b*x=x*raw v b → raw v b*y=y*raw v b →
    b=1 ∧ ∀ i, v i=v 0 := by
  decide +kernel

theorem center_card_le_two : Nat.card (Subgroup.center Group)≤2 := by
  let f : Subgroup.center Group → ZMod 2 := fun z => z.val.val.left.toAdd.val 0
  have detector (z : Subgroup.center Group) :
      z.val.val.right=1 ∧ ∀ i,z.val.val.left.toAdd.val i=z.val.val.left.toAdd.val 0 := by
    have hx := congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.property X).symm)
    have hy := congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.property Y).symm)
    exact center_detector z.val.val.left.toAdd.val z.val.val.right z.val.property hx hy
  have hf : Function.Injective f := by
    intro z w he
    obtain ⟨hz,hvz⟩ := detector z
    obtain ⟨hw,hvw⟩ := detector w
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      exact (hvz i).trans (he.trans (hvw i).symm)
    · exact hz.trans hw.symm
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_zmod] using hc
end SymmetricSubgroupAsymptotics.KleinParitySignedBinaryTop
