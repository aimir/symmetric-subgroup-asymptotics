import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.Basic

/-! If every nonfixed actual orbit has cardinal divisible by q, the
actual action degree is congruent to its fixed-point count modulo q.
This is the orbit decomposition argument, with no p-group or semisimple
assumption. The caller supplies actual orbit divisibility. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteActionOrbitMultipleFixedCongruence
open MulAction Fintype

theorem card_modEq_card_fixedPoints
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (q : ℕ) (hq : 2≤q)
    (hdiv : ∀ x : X, x∉fixedPoints G X → q ∣ Nat.card (orbit G x)) :
    Nat.ModEq q (Nat.card X) (Nat.card (fixedPoints G X)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (fixedPoints G X) := Fintype.ofFinite _
  letI : Fact (1<q) := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  calc
    card X=card (Σ y : Quotient (orbitRel G X), {x // Quotient.mk'' x=y}) :=
      card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G X))).symm
    _=∑ a : Quotient (orbitRel G X), card {x // Quotient.mk'' x=a} := card_sigma
    _ ≡ ∑ _a : fixedPoints G X, 1 [MOD q] := by
      rw [←ZMod.natCast_eq_natCast_iff _ _ q,Nat.cast_sum,Nat.cast_sum]
      have key : ∀ x : X,
          card {y // (Quotient.mk'' y : Quotient (orbitRel G X))=Quotient.mk'' x} =
            card (orbit G x) := fun x => by simp only [Quotient.eq'']; congr
      refine Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1)
          (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
            rw [key,mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
      by_cases hfix : b∈fixedPoints G X
      · exact ⟨⟨b,hfix⟩,Finset.mem_univ _,ne_of_eq_of_ne Nat.cast_one one_ne_zero,rfl⟩
      · exact (hb (by
          rw [key]
          apply (ZMod.natCast_eq_zero_iff _ q).mpr
          simpa only [Nat.card_eq_fintype_card] using hdiv b hfix)).elim
    _=_ := by simp

end SymmetricSubgroupAsymptotics.FiniteActionOrbitMultipleFixedCongruence
