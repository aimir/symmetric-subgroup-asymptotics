import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! A faithful actual permutation group fixing a set pointwise embeds in
the permutations of its exact complement. No ambient subgroup order or
monotonicity of conjugacy-class counts is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FinitePermutationFixedComplementEmbedding
variable {P X : Type*} [Group P] (f : P →* Equiv.Perm X) (S : Set X)
    (hfix : ∀ p : P, ∀ x∈S, f p x=x)
include hfix

private theorem mem_iff (p : P) (x : X) : f p x∈S ↔ x∈S := by
  constructor
  · intro hx
    have hh : (f p)⁻¹ (f p x)=f p x := by
      simpa only [map_inv] using hfix p⁻¹ (f p x) hx
    have hself : (f p)⁻¹ (f p x)=x := (f p).symm_apply_apply x
    have he : x=f p x := hself.symm.trans hh
    exact he.symm ▸ hx
  · intro hx
    rwa [hfix p x hx]

def complementHom : P →* Equiv.Perm {x : X // x∉S} where
  toFun p := (f p).subtypePerm (fun x => not_congr (mem_iff f S hfix p x))
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change f 1 x.val=x.val
    simp only [map_one,Equiv.Perm.one_apply]
  map_mul' p q := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change f (p*q) x.val=f p (f q x.val)
    rw [map_mul]
    rfl

theorem complementHom_injective (hf : Function.Injective f) :
    Function.Injective (complementHom f S hfix) := by
  intro p q h
  apply hf
  ext x
  by_cases hx : x∈S
  · rw [hfix p x hx,hfix q x hx]
  · exact congrArg (fun e : Equiv.Perm {x : X // x∉S} => (e ⟨x,hx⟩).val) h

theorem card_dvd_factorial [Finite P] [Finite X] (hf : Function.Injective f) :
    Nat.card P ∣ (Nat.card {x : X // x∉S}).factorial := by
  rw [←Nat.card_perm]
  exact Subgroup.card_dvd_of_injective (complementHom f S hfix)
    (complementHom_injective f S hfix hf)

theorem nine_not_in_complement_of_card_le_five [Finite P] [Finite X]
    (hf : Function.Injective f) (hP : Nat.card P=9)
    (hsmall : Nat.card {x : X // x∉S}≤5) : False := by
  have hd := card_dvd_factorial f S hfix hf
  rw [hP] at hd
  generalize Nat.card {x : X // x∉S} = m at hd hsmall
  interval_cases m <;> norm_num [Nat.factorial] at hd

end SymmetricSubgroupAsymptotics.FinitePermutationFixedComplementEmbedding
