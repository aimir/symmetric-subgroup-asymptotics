import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-! Literal moments on binary translation coordinates.

Reindexing the original coordinate sum derives the translation and
commutator equations. A nonzero parity character and a surjective
translation coordinate then exclude a nonzero central translation.
These are linear-algebra statements only; an application must still
provide the actual reversible point chart and original quotient.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryTranslationMoments

section Moments

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Fintype V]

def parity : (V → k) →ₗ[k] k where
  toFun f := ∑ v,f v
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' _ _ := by simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]

def moment : (V → k) →ₗ[k] V where
  toFun f := ∑ v,f v • v
  map_add' _ _ := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

def translate (u : V) (f : V → k) : V → k := fun v => f (v-u)

theorem parity_translate (u : V) (f : V → k) :
    parity (translate u f)=parity f := by
  change (∑ v,f (v-u))=∑ v,f v
  have h := Equiv.sum_comp (Equiv.addRight u) (fun v => f (v-u))
  change (∑ v,f ((v+u)-u))=∑ v,f (v-u) at h
  simpa only [add_sub_cancel_right] using h.symm

theorem moment_translate (u : V) (f : V → k) :
    moment (translate u f)=moment f+parity f • u := by
  calc
    moment (translate u f)=∑ v,f v • (v+u) := by
      change (∑ v,f (v-u) • v)=∑ v,f v • (v+u)
      have h := Equiv.sum_comp (Equiv.addRight u) (fun v => f (v-u) • v)
      change (∑ v,f ((v+u)-u) • (v+u))=∑ v,f (v-u) • v at h
      simpa only [add_sub_cancel_right] using h.symm
    _ = moment f+parity f • u := by
      change (∑ v,f v • (v+u))=(∑ v,f v • v)+(∑ v,f v) • u
      simp only [smul_add,Finset.sum_add_distrib,Finset.sum_smul]

/-- The moment of the exact difference of the two affine products. -/
theorem moment_commutator (u v : V) (a b : V → k) :
    moment (translate u b+a-(translate v a+b))=
      parity b • u-parity a • v := by
  rw [map_sub,map_add,map_add,moment_translate,moment_translate]
  abel

theorem moment_const (c : k) :
    moment (fun _ : V => c)=c • ∑ v : V,v := by
  change (∑ v : V,c • v)=c • ∑ v : V,v
  simp only [Finset.smul_sum]

end Moments

section Binary

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem scalar_zero_or_one (c : ZMod 2) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem neg_eq_self (v : V) : -v=v := by
  calc
    -v=(-(1:ZMod 2)) • v := by simp only [neg_smul,one_smul]
    _ = v := by rw [ZMod.neg_eq_self_mod_two,one_smul]

theorem moment_commutator_binary [Fintype V] (u v : V) (a b : V → ZMod 2) :
    moment (translate u b+a-(translate v a+b))=
      parity b • u+parity a • v := by
  rw [moment_commutator,sub_eq_add_neg,neg_eq_self]

/-- One actual surjective translation coordinate suffices. In the
nonzero scalar case the commutator equation would make a vector space
of more than two elements an image of the two-element field. -/
theorem translation_eq_zero_of_nonzero_parity
    [Finite V] {H : Type*} (u : H → V) (hu : Function.Surjective u)
    (χ : H → ZMod 2) (hχ : ∃ h,χ h≠0) (hV : 2<Nat.card V)
    (δ : V) (p : ZMod 2)
    (hcomm : ∀ h,χ h • δ+p • u h=0) : δ=0 := by
  have hp : p=0 ∨ p=1 := scalar_zero_or_one p
  rcases hp with hp | hp
  · obtain ⟨h,hh⟩ := hχ
    have hc : χ h=1 := by
      have hc : χ h=0 ∨ χ h=1 := scalar_zero_or_one (χ h)
      exact hc.resolve_left hh
    simpa only [hp,hc,zero_smul,one_smul,add_zero] using hcomm h
  · have hs : Function.Surjective (fun c : ZMod 2 => c • δ) := by
      intro v
      obtain ⟨h,rfl⟩ := hu v
      refine ⟨χ h,?_⟩
      have he := hcomm h
      rw [hp,one_smul] at he
      have he' : χ h • δ=-(u h) := eq_neg_of_add_eq_zero_left he
      exact he'.trans (neg_eq_self (u h))
    have hcard := Nat.card_le_card_of_surjective (fun c : ZMod 2 => c • δ) hs
    rw [Nat.card_zmod] at hcard
    omega

end Binary

end SymmetricSubgroupAsymptotics.BinaryTranslationMoments
