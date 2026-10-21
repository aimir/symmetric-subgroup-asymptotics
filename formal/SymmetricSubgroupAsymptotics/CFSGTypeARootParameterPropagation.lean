import SymmetricSubgroupAsymptotics.CFSGTypeARootParameterClosure
import SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldScalars

/-! One actual scalar root propagates to all coordinate roots using
unit-root commutators. No point/action correspondence is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootParameterPropagation
open CFSGTypeAElementaryMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

theorem all_roots_of_one_root (hn : 3≤Fintype.card n)
    (H : Subgroup (SL (n:=n) (F:=F)))
    (hOne : ∀ i j : n,∀ hij : i≠j,elementary hij (1 : F)∈H)
    (a b : n) (hab : a≠b) (t : F) (ht : elementary hab t∈H) :
    ∀ i j : n,∀ hij : i≠j,elementary hij t∈H := by
  have hcomm : ∀ x y : SL (n:=n) (F:=F),x∈H→y∈H→⁅x,y⁆∈H := by
    intro x y hx hy
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have row : ∀ j : n,∀ haj : a≠j,elementary haj t∈H := by
    intro j haj
    by_cases hjb : j=b
    · subst j
      exact ht
    have h := hcomm (elementary hab t) (elementary (Ne.symm hjb) 1) ht
      (hOne b j (Ne.symm hjb))
    rw [elementary_commutator hab (Ne.symm hjb) haj,mul_one] at h
    exact h
  have offColumn : ∀ i j : n,∀ (hia : i≠a) (haj : a≠j) (hij : i≠j),elementary hij t∈H := by
    intro i j hia haj hij
    have h := hcomm (elementary hia (1 : F)) (elementary haj t)
      (hOne i a hia) (row j haj)
    rw [elementary_commutator hia haj hij,one_mul] at h
    exact h
  intro i j hij
  by_cases hia : i=a
  · subst i
    exact row j hij
  by_cases hja : j=a
  · subst j
    have hc : 0<(({i,a} : Finset n)ᶜ).card := by
      have hp : ({i,a} : Finset n).card≤2 := Finset.card_le_two
      rw [Finset.card_compl]
      omega
    obtain ⟨k,hk⟩ := Finset.card_pos.mp hc
    have hk' : k≠i ∧ k≠a := by
      simpa only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or] using hk
    have hik : i≠k := Ne.symm hk'.1
    have hka : k≠a := hk'.2
    have h := hcomm (elementary hik t) (elementary hka 1)
      (offColumn i k hia (Ne.symm hka) hik) (hOne k a hka)
    rw [elementary_commutator hik hka hij,mul_one] at h
    exact h
  · exact offColumn i j hia (Ne.symm hja) hij

/-- A primitive scalar needs to be supplied at only one actual root,
in addition to the unit root elements. -/
theorem eq_top_of_one_scalar_root (hn : 3≤Fintype.card n)
    (H : Subgroup (SL (n:=n) (F:=F)))
    (hOne : ∀ i j : n,∀ hij : i≠j,elementary hij (1 : F)∈H)
    (a b : n) (hab : a≠b) (t : F) (ht : elementary hab t∈H)
    (hgen : Subring.closure ({t} : Set F)=⊤) : H=⊤ := by
  apply CFSGTypeARootParameterClosure.eq_top_of_scalar_closure hn H hOne {t} _ hgen
  intro u hu
  have he : u=t := Set.mem_singleton_iff.mp hu
  subst u
  exact all_roots_of_one_root hn H hOne a b hab t ht

end SymmetricSubgroupAsymptotics.CFSGTypeARootParameterPropagation
