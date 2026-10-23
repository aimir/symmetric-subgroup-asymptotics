import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedSliceImages
import SymmetricSubgroupAsymptotics.CFSGQuadraticNonsingularPairCoupling
import SymmetricSubgroupAsymptotics.CFSGQuadraticLocalDifferenceScalars

/-! One actual singular-difference edge in a nonzero norm slice forces
the same normalized image tail. The actual local linear representative
on the spanned singular plane and its fixed hyperbolic difference ray
supply the scalar equation; independence couples the two coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSliceEdgeConstancy
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSliceCoordinates
open CFSGTwistedDNormalizedSliceImages CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticSubspacePoints

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem slice_difference (n : ℕ) (q : CFSG.PrimePower)
    (h k : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (a : q.Extension 2) :
    sliceVector n q h a - sliceVector n q k a = sliceVector n q (h - k) 0 := by
  apply (splitEquiv n q).injective
  rw [map_sub, split_sliceVector, split_sliceVector, split_sliceVector]
  simp only [Prod.mk_sub_mk, sub_self]

theorem normalized_image_eq_of_edge (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))))
    (a : q.Extension 2) (ha : a ≠ 0)
    (h k : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hh : dotProduct h.1 h.2 = -normForm q a)
    (hk : dotProduct k.1 k.2 = -normForm q a)
    (hdiff : dotProduct (h.1 - k.1) (h.2 - k.2) = 0)
    (b c : q.Extension 2)
    (hb : NormalizedImage n q f a ha h hh b)
    (hc : NormalizedImage n q f a ha k hk c) : b = c := by
  classical
  by_cases hsame : h = k
  · subst k
    exact normalized_image_unique n q f a ha h hh b c hb hc
  let A := fixedQuadraticForm n q
  let v := sliceVector n q h a
  let w := sliceVector n q k a
  let d := v - w
  have hv0 : v ≠ 0 := sliceVector_nonzero n q h a (level_vector_nonzero n q a ha h hh)
  have hw0 : w ≠ 0 := sliceVector_nonzero n q k a (level_vector_nonzero n q a ha k hk)
  have hvQ : A v = 0 := by
    change fixedQuadraticForm n q (sliceVector n q h a) = 0
    rw [quadratic_sliceVector, hh, neg_add_cancel]
  have hwQ : A w = 0 := by
    change fixedQuadraticForm n q (sliceVector n q k a) = 0
    rw [quadratic_sliceVector, hk, neg_add_cancel]
  have hdvec : d = sliceVector n q (h - k) 0 := slice_difference n q h k a
  have hdQ : A d = 0 := by
    change fixedQuadraticForm n q d = 0
    rw [hdvec, quadratic_sliceVector, QuadraticMap.map_zero, add_zero]
    exact hdiff
  have hd0 : d ≠ 0 := by
    intro he
    apply hsame
    apply sub_eq_zero.mp
    have hp := congrArg (hyperbolicPart n q) he
    change hyperbolicPart n q (v - w) = hyperbolicPart n q 0 at hp
    dsimp only [v, w] at hp
    rw [map_sub, sliceVector_hyperbolic, sliceVector_hyperbolic, map_zero] at hp
    exact hp
  let P := ray A d hd0 hdQ
  have hdA : anisotropicPart n q d = 0 := by
    change anisotropicPart n q (v - w) = 0
    dsimp only [v, w]
    rw [map_sub, sliceVector_anisotropic, sliceVector_anisotropic, sub_self]
  have hPzero : ∀ z ∈ P.val, anisotropicPart n q z = 0 := by
    intro z hz
    change z ∈ Submodule.span (fixedField q) {d} at hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul, hdA, smul_zero]
  obtain ⟨alpha, beta, gamma, hAlpha0, heq⟩ :=
    CFSGQuadraticLocalDifferenceScalars.exists_scalars A f hlinear
      v w (sliceVector n q h b) (sliceVector n q k c) hv0 hw0 hd0 hvQ hwQ hdQ
      hb hc (hfix P hPzero)
  change alpha • sliceVector n q h b - beta • sliceVector n q k c = gamma • d at heq
  have hQh : hyperbolicForm n q h ≠ 0 := by
    rw [hyperbolicForm_apply, hh]
    exact neg_ne_zero.mpr (normForm_ne_zero q ha)
  have hQdiff : hyperbolicForm n q (h - k) = 0 := by
    rw [hyperbolicForm_apply]
    exact hdiff
  have hind := CFSGQuadraticNonsingularPairCoupling.independent_of_singular_difference
    (hyperbolicForm n q) h k hQh hsame hQdiff
  have hprod := congrArg (splitEquiv n q) heq
  rw [map_sub, map_smul, map_smul, map_smul, split_sliceVector, split_sliceVector] at hprod
  have hdSplit : splitEquiv n q d = (h - k, (0 : q.Extension 2)) := by rw [hdvec, split_sliceVector]
  rw [hdSplit] at hprod
  exact CFSGQuadraticNonsingularPairCoupling.tail_eq_of_coupled_difference
    h k hind b c alpha beta gamma hAlpha0 hprod

end SymmetricSubgroupAsymptotics.CFSGTwistedDSliceEdgeConstancy
