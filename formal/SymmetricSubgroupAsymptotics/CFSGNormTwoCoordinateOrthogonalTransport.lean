import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootOrbitTransitive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNegation
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns

/-! A small positive orthogonal-root witness at ONE original root
transports to a uniform commuting-root bound at every original root.
Actual Weyl words preserve the integer pairing; positive representatives
of distinct original positive roots cannot collide by opposite signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTransport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootCentralizerCardinality
open CFSGNormTwoCoordinateRootOrbitTransitive CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGIntegralNormTwoSigns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def positiveRepresentative (k : Roots A) : PositiveRoot A := by
  classical
  by_cases hk : ∀i,0≤k.val i
  · exact ⟨k,hk⟩
  · refine ⟨negativeIndex A hs hp k,?_⟩
    have heven (i : Fin r) : Even (A i i) := by rw [hd i];exact ⟨1,rfl⟩
    have hn := (norm_two_coordinates_one_sign A hs hp heven ho k.val k.property).resolve_left hk
    intro i
    simpa only [negative_val,Pi.neg_apply] using neg_nonneg.mpr (hn i)

theorem positiveRepresentative_val (k : Roots A) :
    (positiveRepresentative A hd hs hp ho k).val.val=k.val ∨
      (positiveRepresentative A hd hs hp ho k).val.val= -k.val := by
  classical
  unfold positiveRepresentative
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (negative_val A hs hp k)

theorem positive_roots_ne_negative (k l : PositiveRoot A) : k.val.val≠ -l.val.val := by
  intro he
  have hz : k.val.val=0 := by
    funext i
    have hk := k.property i
    have hl := l.property i
    have hi := congrFun he i
    change k.val.val i= -l.val.val i at hi
    change k.val.val i=0
    omega
  have hn := k.val.property
  rw [hz,map_zero] at hn
  norm_num at hn

theorem positiveRepresentative_eq_implies (k l : Roots A)
    (he : positiveRepresentative A hd hs hp ho k=positiveRepresentative A hd hs hp ho l) :
    k.val=l.val ∨ k.val= -l.val := by
  have hv := congrArg (fun x : PositiveRoot A=>x.val.val) he
  rcases positiveRepresentative_val A hd hs hp ho k with hk|hk <;>
    rcases positiveRepresentative_val A hd hs hp ho l with hl|hl
  · exact Or.inl (hk.symm.trans (hv.trans hl))
  · exact Or.inr (hk.symm.trans (hv.trans hl))
  · right
    have hh := hk.symm.trans (hv.trans hl)
    simpa only [neg_neg] using congrArg Neg.neg hh
  · exact Or.inl (neg_injective (hk.symm.trans (hv.trans hl)))

theorem transported_positive_injective {m : ℕ} (w : List (Fin r))
    (f : Fin m→PositiveRoot A) (hf : Function.Injective f) :
    Function.Injective (fun t=>positiveRepresentative A hd hs hp ho
      (wordRoot A hs hp b₀ s₀ w (f t).val)) := by
  intro t s he
  rcases positiveRepresentative_eq_implies A hd hs hp ho _ _ he with h|h
  · apply hf
    apply Subtype.ext
    apply Subtype.ext
    apply (wordLinear A hs hp b₀ s₀ w).injective
    simpa only [wordLinear_root] using h
  · have hlin : wordLinear A hs hp b₀ s₀ w (f t).val.val=
        wordLinear A hs hp b₀ s₀ w (-(f s).val.val) := by
      simpa only [map_neg,wordLinear_root] using h
    exact (positive_roots_ne_negative A (f t) (f s)
      ((wordLinear A hs hp b₀ s₀ w).injective hlin)).elim

include hd hs hp ho in
theorem uniform_commuting_card_of_orthogonal_witness {m : ℕ} (a : Roots A)
    (f : Fin m→PositiveRoot A) (hf : Function.Injective f)
    (horth : ∀t,integerPairing A (f t).val.val a.val=0) (k : Roots A) :
    m≤(commutingPositiveRoots A k).card := by
  classical
  obtain ⟨w,hw⟩ := exists_word_root_to_root A hd hs hp ho a k
  let g : Fin m→PositiveRoot A := fun t=>positiveRepresentative A hd hs hp ho
    (wordRoot A hs hp b₀ s₀ w (f t).val)
  have hg := transported_positive_injective A hd hs hp ho w f hf
  have hpair (t : Fin m) : integerPairing A (g t).val.val k.val=0 := by
    have hh := wordRoot_integer_pairing A hs hp b₀ s₀ w (f t).val a
    rw [hw,horth] at hh
    rcases positiveRepresentative_val A hd hs hp ho
        (wordRoot A hs hp b₀ s₀ w (f t).val) with h|h
    · change integerPairing A (positiveRepresentative A hd hs hp ho _).val.val k.val=0
      rw [h]
      exact hh
    · change integerPairing A (positiveRepresentative A hd hs hp ho _).val.val k.val=0
      rw [h,map_neg,LinearMap.neg_apply,hh,neg_zero]
  let enc : Fin m→commutingPositiveRoots A k := fun t=>
    ⟨g t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl (hpair t)⟩⟩
  have henc : Function.Injective enc := by
    intro t s he
    apply hg
    exact congrArg Subtype.val he
  have hc := Nat.card_le_card_of_injective enc henc
  simpa only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin,Fintype.card_coe] using hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTransport
