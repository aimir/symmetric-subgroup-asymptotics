import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import Mathlib.Algebra.Ring.Subring.Basic

/-! Scalar closure of actual type-A root groups. Steinberg commutators
supply multiplication of parameters, in addition to additive root laws.
This is generic infrastructure, not an assumed two-generator theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootParameterClosure
open CFSGTypeAElementaryMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

private theorem exists_third (hn : 3≤Fintype.card n) (i j : n) :
    ∃ k : n,i≠k ∧ k≠j := by
  have hp : ({i,j} : Finset n).card≤2 := Finset.card_le_two
  have hc : 0<(({i,j} : Finset n)ᶜ).card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨k,hk⟩ := Finset.card_pos.mp hc
  have hk' : k≠i ∧ k≠j := by
    simpa only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or] using hk
  exact ⟨k,Ne.symm hk'.1,hk'.2⟩

/-- Parameters available in every actual root group form a subring once
the unit root elements are present. -/
def rootParameters (hn : 3≤Fintype.card n) (H : Subgroup (SL (n:=n) (F:=F)))
    (hOne : ∀ i j : n,∀ hij : i≠j,elementary hij (1 : F)∈H) : Subring F where
  carrier := {a | ∀ i j : n,∀ hij : i≠j,elementary hij a∈H}
  zero_mem' := by
    intro i j hij
    rw [elementary_zero]
    exact H.one_mem
  one_mem' := hOne
  add_mem' := by
    intro a b ha hb i j hij
    rw [elementary_add]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  neg_mem' := by
    intro a ha i j hij
    rw [←elementary_inv]
    exact H.inv_mem (ha i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k,hik,hkj⟩ := exists_third hn i j
    rw [←elementary_commutator hik hkj hij a b,commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (ha i k hik) (hb k j hkj))
      (H.inv_mem (ha i k hik))) (H.inv_mem (hb k j hkj))

/-- Root parameters extend through the actual generated scalar subring. -/
theorem elementary_mem_of_scalar_closure (hn : 3≤Fintype.card n)
    (H : Subgroup (SL (n:=n) (F:=F)))
    (hOne : ∀ i j : n,∀ hij : i≠j,elementary hij (1 : F)∈H)
    (T : Set F) (hT : ∀ a∈T,∀ i j : n,∀ hij : i≠j,elementary hij a∈H)
    (a : F) (ha : a∈Subring.closure T) (i j : n) (hij : i≠j) : elementary hij a∈H := by
  have hle : Subring.closure T≤rootParameters hn H hOne := Subring.closure_le.mpr hT
  exact hle ha i j hij

/-- The scalar-generation and root-generation obligations combine into
an exact subgroup equality inside the literal SL group. -/
theorem eq_top_of_scalar_closure (hn : 3≤Fintype.card n)
    (H : Subgroup (SL (n:=n) (F:=F)))
    (hOne : ∀ i j : n,∀ hij : i≠j,elementary hij (1 : F)∈H)
    (T : Set F) (hT : ∀ a∈T,∀ i j : n,∀ hij : i≠j,elementary hij a∈H)
    (hgen : Subring.closure T=⊤) : H=⊤ := by
  apply CFSGTypeAElementaryGeneration.eq_top_of_elementary H
  intro i j hij a
  apply elementary_mem_of_scalar_closure hn H hOne T hT a _ i j hij
  rw [hgen]
  trivial

end SymmetricSubgroupAsymptotics.CFSGTypeARootParameterClosure
