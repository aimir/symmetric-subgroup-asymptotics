import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedPartialIsometry
import SymmetricSubgroupAsymptotics.CFSGHermitianCodimensionOneExtension
import SymmetricSubgroupAsymptotics.CFSGHermitianFullRankExtension
import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity

/-! Extend the ACTUAL opposed local linear pieces to an ambient
isometry in every original unitary rank at least three. The second
piece is rescaled by its derived cross multiplier, which changes no
point. Both ambient parity cases are discharged on the signed form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem unitaryNaturalPair_nondegenerate (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r+1) → q.Extension 2) (hx : ∀ y, unitaryNaturalPair q r x y = 0) : x = 0 := by
  by_contra hne
  obtain ⟨y,hy⟩ := hermitianPair_surjective (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r) x hne 1
  exact one_ne_zero (hy.symm.trans (hx y))

theorem exists_unitary_opposed_isometry_extension (q : CFSG.PrimePower) (r : ℕ) (hr : 3 ≤ r)
    (f : Equiv.Perm (SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f)
    (F : SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f
      (unitaryStandardIsotropicSpace q r) (RingEquiv.refl (q.Extension 2)))
    (G : SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f
      (unitaryOppositeIsotropicSpace q r) (RingEquiv.refl (q.Extension 2))) :
    ∃ c : q.Extension 2, c ≠ 0 ∧
      ∃ e : (Fin (r+1) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (r+1) → q.Extension 2),
        (∀ x y, unitaryNaturalPair q r (e x) (e y) = unitaryNaturalPair q r x y) ∧
        (∀ p : unitaryStandardSingularSpace q r, e p.val = F.map p) ∧
        ∀ z : unitaryOppositeSingularSpace q r, e z.val = c⁻¹ • G.map z := by
  obtain ⟨c,hc,A,hA,hP,hZ⟩ := exists_unitary_opposed_partial_isometry q r hr f hf F G
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) r := signedReversalUnit (q.Extension 2) r
  let W := (unitaryOpposedSource q r).range
  have hW : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sig H x y = 0) → x = 0 :=
    unitaryOpposedSource_range_nondegenerate q r
  have hext : ∃ e : (Fin (r+1) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (r+1) → q.Extension 2),
      (∀ x y, unitaryNaturalPair q r (e x) (e y) = unitaryNaturalPair q r x y) ∧
      ∀ w : W, e w.val = A w := by
    rcases Nat.even_or_odd r with hEven | hOdd
    · have hdim : Module.finrank (q.Extension 2) W + 1 = Fintype.card (Fin (r+1)) := by
        change Module.finrank (q.Extension 2) (unitaryOpposedSource q r).range + 1 = _
        rw [unitaryOpposedSource_range_finrank,Fintype.card_fin]
        obtain ⟨k,hk⟩ := hEven
        omega
      have hfixed (x : Fin (r+1) → q.Extension 2) :
          sig (hermitianPair sig H x x) = hermitianPair sig H x x := by
        have hh := unitaryNaturalPair_signed_reciprocal q r x x
        have hs : (-1 : q.Extension 2)^r = 1 := hEven.neg_one_pow
        rw [hs,one_mul] at hh
        exact hh.symm
      have hnorm (t : q.Extension 2) (_ : t ≠ 0) (ht : sig t = t) :
          ∃ a : q.Extension 2, sig a * a = t := by
        obtain ⟨a,ha⟩ := CFSGTwistedA2UnipotentArrays.exists_norm_eq_fixed q t ht
        exact ⟨a,(mul_comm _ _).trans ha⟩
      exact CFSGHermitianCodimensionOneExtension.exists_extension sig H W A hW
        (unitaryNaturalPair_nondegenerate q r) (unitaryNaturalPair_zero_swap q r) hA hdim hfixed hnorm
    · have hdim : Module.finrank (q.Extension 2) W = Fintype.card (Fin (r+1)) := by
        change Module.finrank (q.Extension 2) (unitaryOpposedSource q r).range = _
        rw [unitaryOpposedSource_range_finrank,Fintype.card_fin]
        obtain ⟨k,hk⟩ := hOdd
        omega
      exact CFSGHermitianFullRankExtension.exists_extension sig H W A hW hA hdim
  obtain ⟨e,heform,he⟩ := hext
  refine ⟨c,hc,e,heform,?_,?_⟩
  · intro p
    have hh := he (LinearEquiv.ofInjective (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) (p,0))
    change e (p.val+0) = A (LinearEquiv.ofInjective (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) (p,0)) at hh
    rw [add_zero,hP] at hh
    exact hh
  · intro z
    have hh := he (LinearEquiv.ofInjective (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) (0,z))
    change e (0+z.val) = A (LinearEquiv.ofInjective (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) (0,z)) at hh
    rw [zero_add,hZ] at hh
    exact hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
