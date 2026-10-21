import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A finite function constant on actual right H-translates is counted
over the original left cosets with their common actual H multiplicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGUniformCosetSum

theorem sum_eq_card_subgroup_mul_sum_quotient {A : Type*} [Group A] [Fintype A]
    (H : Subgroup A) (f : A → ℕ) (hf : ∀ (a : A) (h : H),f (a*h)=f a) :
    (∑ a : A,f a)=Fintype.card H*∑ q : A ⧸ H,f q.out := by
  let lift : (A ⧸ H)×H → A := fun p => p.1.out*p.2
  have hcoset (q : A ⧸ H) (h : H) : ((q.out*(h : A) : A) : A ⧸ H)=q := by
    calc
      _ = (q.out : A ⧸ H) := QuotientGroup.eq.mpr (by
        simpa [mul_inv_rev,mul_assoc] using H.inv_mem h.property)
      _ = q := Quotient.out_eq q
  have hlift : Function.Bijective lift := by
    constructor
    · rintro ⟨q,h⟩ ⟨r,k⟩ he
      have hqr : q=r := by
        calc
          q = ((lift (q,h) : A) : A ⧸ H) := (hcoset q h).symm
          _ = ((lift (r,k) : A) : A ⧸ H) := congrArg QuotientGroup.mk he
          _ = r := hcoset r k
      subst r
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel he))
    · intro a
      let q : A ⧸ H := a
      have hmem : q.out⁻¹*a∈H := QuotientGroup.eq.mp (Quotient.out_eq q)
      refine ⟨(q,⟨q.out⁻¹*a,hmem⟩),?_⟩
      exact mul_inv_cancel_left q.out a
  let e : A ≃ (A ⧸ H)×H := (Equiv.ofBijective lift hlift).symm
  have hp : ∀ p : (A ⧸ H)×H,f (e.symm p)=f p.1.out := by
    rintro ⟨q,h⟩
    change f (q.out*(h : A))=f q.out
    exact hf q.out h
  calc
    (∑ a : A,f a)=(∑ p : (A ⧸ H)×H,f (e.symm p)) := (Equiv.sum_comp e.symm f).symm
    _ = ∑ p : (A ⧸ H)×H,f p.1.out := Finset.sum_congr rfl (fun p _ => hp p)
    _ = Fintype.card H*∑ q : A ⧸ H,f q.out := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
      exact (Finset.mul_sum _ _ _).symm

end SymmetricSubgroupAsymptotics.CFSGUniformCosetSum
