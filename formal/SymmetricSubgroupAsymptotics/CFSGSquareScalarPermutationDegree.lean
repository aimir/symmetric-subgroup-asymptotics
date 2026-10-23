import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSignedSquares
import SymmetricSubgroupAsymptotics.CFSGEqualClassPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGUniformCosetSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Units

/-! Burnside's weighted average for the two square-scalar classes of a
finite field. The fixed counts belong to the original additive action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
open MulAction

private theorem average_identity {k L M c S q : ℕ}
    (hLM : L=M) (hMc : M=c*S) (hkc : k*c=q) : k*L=q*S := by
  calc
    k*L=k*M := congrArg (fun n : ℕ => k*n) hLM
    _=k*(c*S) := congrArg (fun n : ℕ => k*n) hMc
    _=(k*c)*S := (Nat.mul_assoc k c S).symm
    _=q*S := congrArg (fun n : ℕ => n*S) hkc

private theorem degree_le_coset_index_mul {P A X : Type*}
    [Group P] [Group A] [Fintype P] [Fintype A] [Fintype X] [MulAction P X]
    (H : Subgroup A) (f : A→ℕ)
    (hinv : ∀ (a : A) (h : H), f (a*h)=f a)
    (hfix : ∀ a,f a<Fintype.card X)
    (hA : Fintype.card A=Fintype.card P-1)
    (hsum : (∑ a ∈ (Finset.univ : Finset P).erase 1,
      Fintype.card (fixedBy X a))=∑ a : A,f a) :
    Nat.card P≤H.index*Nat.card X := by
  let S : ℕ := ∑ q : A ⧸ H,f q.out
  have hS : S<H.index*Fintype.card X := by
    have hh := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty :
        (Finset.univ : Finset (A ⧸ H)).Nonempty) (fun q _ => hfix q.out)
    simpa only [S,Finset.sum_const,Finset.card_univ,smul_eq_mul,
      ←Nat.card_eq_fintype_card] using hh
  have hcos : (∑ a : A,f a)=Fintype.card H*S :=
    CFSGUniformCosetSum.sum_eq_card_subgroup_mul_sum_quotient H f hinv
  have hcard : H.index*Fintype.card H=Fintype.card P-1 := by
    have hh := H.card_mul_index
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at hh
    rw [Nat.mul_comm] at hh
    exact hh.trans hA
  have hav : H.index*(∑ a ∈ (Finset.univ : Finset P).erase 1,
      Fintype.card (fixedBy X a))=(Fintype.card P-1)*S :=
    average_identity (k:=H.index)
      (L:=∑ a ∈ (Finset.univ : Finset P).erase 1,Fintype.card (fixedBy X a))
      (M:=∑ a : A,f a) (c:=Fintype.card H) (S:=S) (q:=Fintype.card P-1)
      hsum hcos hcard
  exact CFSGConjugateSubgroupDegree.card_le_mul_of_fixedBy_average H.index S hS hav

variable {F X : Type*} [Field F] [Fintype F] [Fintype X]
    [MulAction (Multiplicative F) X]

set_option maxHeartbeats 800000 in
theorem card_le_twice_of_square_fixedBy
    (hsquare : ∀ (a c : Fˣ),
      Nat.card (fixedBy X (Multiplicative.ofAdd ((a : F)*(c : F)^2)))=
        Nat.card (fixedBy X (Multiplicative.ofAdd (a : F))))
    (hmove : ∀ a : Fˣ, ∃ x : X, Multiplicative.ofAdd (a : F) • x≠x) :
    Nat.card F≤2*Nat.card X := by
  let H : Subgroup Fˣ := (powMonoidHom 2 : Fˣ→*Fˣ).range
  let f : Fˣ→ℕ := fun a => Fintype.card (fixedBy X (Multiplicative.ofAdd (a : F)))
  have hinv : ∀ (a : Fˣ) (h : H), f (a*h)=f a := by
    intro a h
    obtain ⟨c,hc⟩ := h.property
    have hc' : c^2=(h : Fˣ) := hc
    rw [←hc']
    simpa only [f,Units.val_mul,Units.val_pow_eq_pow_val,Nat.card_eq_fintype_card] using hsquare a c
  have hk : H.index≤2 := by
    change (powMonoidHom 2 : Fˣ→*Fˣ).range.index≤2
    rw [IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_le_right _ (by decide)
  have hfix (a : Fˣ) : f a<Fintype.card X := by
    obtain ⟨x,hx⟩ := hmove a
    apply Fintype.card_lt_of_injective_of_notMem
      (fun y : fixedBy X (Multiplicative.ofAdd (a : F)) => y.val)
      Subtype.val_injective (b:=x)
    rintro ⟨y,rfl⟩
    exact hx y.property
  have hsum : (∑ a ∈ (Finset.univ : Finset (Multiplicative F)).erase 1,
      Fintype.card (fixedBy X a))=∑ a : Fˣ,f a := by
    symm
    change (∑ a ∈ (Finset.univ : Finset Fˣ), f a)=_
    apply Finset.sum_bij (fun (a : Fˣ) _ => Multiplicative.ofAdd (a : F))
    · intro a _
      simp only [Finset.mem_erase,Finset.mem_univ,and_true]
      intro he
      exact a.ne_zero (congrArg Multiplicative.toAdd he)
    · intro a _ b _ he
      exact Units.ext (congrArg Multiplicative.toAdd he)
    · intro b hb
      have hb0 : b.toAdd≠0 := by
        intro he
        exact (Finset.mem_erase.mp hb).1 (congrArg Multiplicative.ofAdd he)
      exact ⟨Units.mk0 b.toAdd hb0,Finset.mem_univ _,rfl⟩
    · intro a _
      rfl
  have hA : Fintype.card Fˣ=Fintype.card (Multiplicative F)-1 := by
    simp only [Fintype.card_units,Fintype.card_multiplicative]
  have hh : Nat.card (Multiplicative F)≤H.index*Nat.card X :=
    degree_le_coset_index_mul H f hinv hfix hA hsum
  have hp : Nat.card (Multiplicative F)=Nat.card F := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative]
  rw [hp] at hh
  exact hh.trans (Nat.mul_le_mul_right (Nat.card X) hk)

end SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree

/-! The three-modulo-four refinement preserves the two-class API above. -/
namespace SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
open MulAction CFSGConjugateSubgroupDegree CFSGFiniteFieldSignedSquares

theorem field_card_le_of_root_movement {K G X : Type*}
    [Field K] [Finite K] [Group G] [Finite X] [MulAction G X]
    (hcard : Nat.card K % 4=3) (root : Multiplicative K→*G)
    (torus : Kˣ→G)
    (hact : ∀t a, torus t*root (Multiplicative.ofAdd a)*(torus t)⁻¹=
      root (Multiplicative.ofAdd (a*(t:K)^2)))
    (hmove : ∃x : X, root (Multiplicative.ofAdd 1) • x≠x) :
    Nat.card K≤Nat.card X := by
  classical
  letI : MulAction (Multiplicative K) X := MulAction.compHom X root
  rw [←show Nat.card (Multiplicative K)=Nat.card K from Nat.card_congr Multiplicative.toAdd]
  apply card_le_of_constant_fixedBy
    (Nat.card (fixedBy X (root (Multiplicative.ofAdd 1))))
  · intro a ha
    have ha0 : a.toAdd≠0 := by
      intro he
      exact ha (congrArg Multiplicative.ofAdd he)
    obtain ⟨t,ht⟩ := eq_square_or_neg_square K hcard a.toAdd ha0
    have he := Nat.card_congr (fixedByConjugateEquiv (X:=X)
      (root (Multiplicative.ofAdd 1)) (torus t))
    rw [hact,one_mul] at he
    have hf : Nat.card (fixedBy X (root a))=
        Nat.card (fixedBy X (root (Multiplicative.ofAdd 1))) := by
      rcases ht with ht | ht
      · have heq : root a=root (Multiplicative.ofAdd ((t:K)^2)) :=
          congrArg (fun z:K=>root (Multiplicative.ofAdd z)) ht
        exact (congrArg (fun g:G=>Nat.card (fixedBy X g)) heq).trans he.symm
      · have heq : root a=(root (Multiplicative.ofAdd ((t:K)^2)))⁻¹ := by
          rw [←map_inv]
          exact congrArg (fun z:K=>root (Multiplicative.ofAdd z)) ht
        rw [heq,fixedBy_inv]
        exact he.symm
    simpa only [MulAction.fixedBy,MulAction.compHom_smul_def] using hf
  · obtain ⟨x,hx⟩ := hmove
    exact ⟨Multiplicative.ofAdd 1,x,hx⟩

end SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
