import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentCommutator

/-! An actual subgroup containing one unipotent at every first parameter
contains the whole original U. The second parameters may be arbitrary:
actual commutators recover every central parameter. A primitive scaling
then makes one nonzero first parameter sufficient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters

theorem unipotent_le_of_first_surjective (m : ℕ) (hm : 1≤m)
    (H : Subgroup (Ambient m))
    (hfirst : ∀ a : Field m,∃ b : Field m,unipotentElement m a b∈H) :
    unipotentSubgroup m≤H := by
  have hz : ∀ z : Field m,unipotentElement m 0 z∈H := by
    intro z
    obtain ⟨a,c,hac⟩ := every_central_parameter_is_commutator m hm z
    obtain ⟨b,hb⟩ := hfirst a
    obtain ⟨d,hd⟩ := hfirst c
    have he : ⁅unipotentElement m a b,unipotentElement m c d⁆=unipotentElement m 0 z := by
      rw [unipotentElement_commutator]
      rw [unipotentElement_commutator] at hac
      exact hac
    rw [←he,commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hb hd) (H.inv_mem hb)) (H.inv_mem hd)
  rintro g ⟨a,b,rfl⟩
  obtain ⟨d,hd⟩ := hfirst a
  have hh := H.mul_mem hd (hz (b+d))
  rw [unipotentElement_mul] at hh
  have he : d+(b+d)+theta m a*0=b := by
    rw [mul_zero,add_zero,add_comm b d,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  simpa only [add_zero,he] using hh

/-- This uses the original conjugation relation, not a surrogate cyclic
module or an ordinary-rank substitute. -/
theorem first_surjective_of_primitive_scaling (m : ℕ)
    (H : Subgroup (Ambient m)) (h : Ambient m) (hh : h∈H)
    (l : (Field m)ˣ) (hl : ∀ c : (Field m)ˣ,c∈Subgroup.zpowers l)
    (u : Field m)
    (hscale : ∀ x y : Field m,
      h*unipotentElement m x y*h⁻¹=unipotentElement m ((l : Field m)*x) (u*y))
    (a b : Field m) (ha : a≠0) (hab : unipotentElement m a b∈H) :
    ∀ c : Field m,∃ d : Field m,unipotentElement m c d∈H := by
  have hpow : ∀ k : ℕ,unipotentElement m ((l : Field m)^k*a) (u^k*b)∈H := by
    intro k
    induction k with
    | zero => simpa only [pow_zero,one_mul] using hab
    | succ k ih =>
      have hk := H.mul_mem (H.mul_mem hh ih) (H.inv_mem hh)
      rw [hscale] at hk
      simpa only [pow_succ',mul_assoc] using hk
  intro c
  by_cases hc : c=0
  · subst c
    exact ⟨0,by rw [unipotentElement_zero];exact H.one_mem⟩
  let d : (Field m)ˣ := Units.mk0 (c/a) (div_ne_zero hc ha)
  obtain ⟨k,hk⟩ := mem_powers_iff_mem_zpowers.mpr (hl d)
  have he : (l : Field m)^k=c/a := by
    have hv := congrArg (fun x : (Field m)ˣ => (x : Field m)) hk
    simpa only [Units.val_pow_eq_pow_val,Units.val_mk0,d] using hv
  refine ⟨u^k*b,?_⟩
  have hka := hpow k
  rw [he,div_mul_cancel₀ c ha] at hka
  exact hka

theorem unipotent_le_of_primitive_scaling (m : ℕ) (hm : 1≤m)
    (H : Subgroup (Ambient m)) (h : Ambient m) (hh : h∈H)
    (l : (Field m)ˣ) (hl : ∀ c : (Field m)ˣ,c∈Subgroup.zpowers l)
    (u : Field m)
    (hscale : ∀ x y : Field m,
      h*unipotentElement m x y*h⁻¹=unipotentElement m ((l : Field m)*x) (u*y))
    (a b : Field m) (ha : a≠0) (hab : unipotentElement m a b∈H) :
    unipotentSubgroup m≤H :=
  unipotent_le_of_first_surjective m hm H
    (first_surjective_of_primitive_scaling m H h hh l hl u hscale a b ha hab)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
