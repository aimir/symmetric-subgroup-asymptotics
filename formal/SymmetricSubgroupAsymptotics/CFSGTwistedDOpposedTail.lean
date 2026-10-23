import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankFixedPairFrame
import SymmetricSubgroupAsymptotics.CFSGHyperbolicTailDisjoint
import SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSpaceOrbit

/-! The exact same-form tail of an opposed pair remains opposed.
Positive and negative first axes are explicit; subtracting their head
components proves disjointness, and rank-nullity proves the second
space also loses exactly one dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedTail
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPolePolar CFSGTwistedDSingularTailDimension
open CFSGTwistedDSingularDimensionBound CFSGTwistedDAllRankFixedPairFrame
open CFSGTwistedDHyperbolicTripleBridge CFSGTwistedA2FixedField

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem pole_firstAxis (n : ℕ) (q : CFSG.PrimePower) :
    poleEquiv n q (firstAxis (n + 1) q) = (1, (0, 0)) := by
  apply Prod.ext
  · apply Subtype.ext
    change (Pi.single (Sum.inl (0 : Fin (n + 3))) (1 : q.Extension 2) :
      CFSGOrthogonalDSerreMatrices.Index (n + 3) → q.Extension 2) (Sum.inl 0) = 1
    exact Pi.single_eq_same _ _
  · apply Prod.ext
    · exact tail_fixedFirst_zero n q
    · apply Subtype.ext
      change (Pi.single (Sum.inl (0 : Fin (n + 3))) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index (n + 3) → q.Extension 2) (Sum.inr 0) = 0
      simp only [Pi.single_apply, Sum.inr_ne_inl, if_false]

theorem pole_negativeFirst (n : ℕ) (q : CFSG.PrimePower) :
    poleEquiv n q (negativeFirst (n + 1) q) = (0, (0, 1)) := by
  apply Prod.ext
  · apply Subtype.ext
    change (Pi.single (Sum.inr (0 : Fin (n + 3))) (1 : q.Extension 2) :
      CFSGOrthogonalDSerreMatrices.Index (n + 3) → q.Extension 2) (Sum.inl 0) = 0
    simp only [Pi.single_apply, Sum.inl_ne_inr, if_false]
  · apply Prod.ext
    · change tailLinear n q (negativeFirst (n + 1) q) = 0
      apply Subtype.ext
      funext i
      cases i <;>
        simp [tailLinear, CFSGOrthogonalDIndexTailCoordinates.tailRestriction,
          CFSGOrthogonalDIndexTailCoordinates.tailIndex, negativeFirst,
          CFSGTwistedDRootPlaneImage.negativeBasis]
    · apply Subtype.ext
      change (Pi.single (Sum.inr (0 : Fin (n + 3))) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index (n + 3) → q.Extension 2) (Sum.inr 0) = 1
      exact Pi.single_eq_same _ _

theorem positiveHead_zero (n : ℕ) (q : CFSG.PrimePower)
    (R : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hs : ∀ v ∈ R, fixedQuadraticForm (n + 1) q v = 0)
    (hf : negativeFirst (n + 1) q ∈ R)
    (v : fixedSpace (n + 1) q) (hv : v ∈ R) : positiveHead n q v = 0 := by
  have hp : (fixedQuadraticForm (n + 1) q).polarBilin (negativeFirst (n + 1) q) v = 0 := by
    change fixedQuadraticForm (n + 1) q (negativeFirst (n + 1) q + v) -
      fixedQuadraticForm (n + 1) q (negativeFirst (n + 1) q) -
        fixedQuadraticForm (n + 1) q v = 0
    rw [hs _ (R.add_mem hf hv), hs _ hf, hs _ hv]
    ring
  rw [negativeFirst_succ, negative_axis_polar] at hp
  exact hp

theorem negative_tail_singular (n : ℕ) (q : CFSG.PrimePower)
    (R : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hs : ∀ v ∈ R, fixedQuadraticForm (n + 1) q v = 0)
    (hf : negativeFirst (n + 1) q ∈ R) :
    ∀ v ∈ R.map (tailLinear n q), fixedQuadraticForm n q v = 0 := by
  rintro v ⟨w, hw, rfl⟩
  have he := hs w hw
  rw [quadratic_coordinates, positiveHead_zero n q R hs hf w hw, zero_mul, zero_add] at he
  exact he

theorem negative_tail_finrank (n : ℕ) (q : CFSG.PrimePower)
    (R : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hs : ∀ v ∈ R, fixedQuadraticForm (n + 1) q v = 0)
    (hf : negativeFirst (n + 1) q ∈ R) :
    Module.finrank (fixedField q) (R.map (tailLinear n q)) + 1 =
      Module.finrank (fixedField q) R := by
  let f := (tailLinear n q).comp R.subtype
  have hk : f.ker.map R.subtype = Submodule.span (fixedField q) {negativeFirst (n + 1) q} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change tailLinear n q x.val = 0 at hx
      have he : x.val = negativeHead n q x.val • negativeFirst (n + 1) q := by
        apply (poleEquiv n q).injective
        rw [map_smul, pole_negativeFirst]
        change (positiveHead n q x.val, (tailLinear n q x.val, negativeHead n q x.val)) = _
        rw [positiveHead_zero n q R hs hf x.val x.property, hx]
        simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, mul_zero]
      exact Submodule.mem_span_singleton.mpr ⟨negativeHead n q x.val, he.symm⟩
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      refine ⟨⟨a • negativeFirst (n + 1) q, R.smul_mem a hf⟩, ?_, rfl⟩
      change tailLinear n q (a • negativeFirst (n + 1) q) = 0
      have ht : tailLinear n q (negativeFirst (n + 1) q) = 0 :=
        congrArg (fun x : fixedField q × (fixedSpace n q × fixedField q) => x.2.1)
          (pole_negativeFirst n q)
      rw [map_smul, ht, smul_zero]
  have hker : Module.finrank (fixedField q) f.ker = 1 :=
    (Submodule.finrank_map_subtype_eq R f.ker).symm.trans
      ((congrArg (fun T : Submodule (fixedField q) (fixedSpace (n + 1) q) =>
        Module.finrank (fixedField q) T) hk).trans
          (finrank_span_singleton (negativeFirst_nonzero (n + 1) q)))
  have hr : f.range = R.map (tailLinear n q) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hd := LinearMap.finrank_range_add_finrank_ker (K := fixedField q)
    (V := R) (V₂ := fixedSpace n q) f
  rw [hr, hker] at hd
  exact hd

theorem disjoint_tails (n : ℕ) (q : CFSG.PrimePower)
    (P R : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hP : ∀ v ∈ P, fixedQuadraticForm (n + 1) q v = 0)
    (hR : ∀ v ∈ R, fixedQuadraticForm (n + 1) q v = 0)
    (he : firstAxis (n + 1) q ∈ P) (hf : negativeFirst (n + 1) q ∈ R)
    (hdis : Disjoint P R) : Disjoint (P.map (tailLinear n q)) (R.map (tailLinear n q)) := by
  let e := poleEquiv n q
  have hd := Submodule.disjoint_map (f := e.toLinearMap) e.injective hdis
  have hPE : (1, ((0 : fixedSpace n q), (0 : fixedField q))) ∈ P.map e.toLinearMap :=
    ⟨firstAxis (n + 1) q, he, pole_firstAxis n q⟩
  have hRF : (0, ((0 : fixedSpace n q), (1 : fixedField q))) ∈ R.map e.toLinearMap :=
    ⟨negativeFirst (n + 1) q, hf, pole_negativeFirst n q⟩
  have ht := CFSGHyperbolicTailDisjoint.disjoint_tails (P.map e.toLinearMap) (R.map e.toLinearMap)
    hd hPE hRF (by
      rintro x ⟨v, hv, rfl⟩
      exact negativeHead_zero n q P hP he v hv) (by
      rintro x ⟨v, hv, rfl⟩
      exact positiveHead_zero n q R hR hf v hv)
  have hcomp : CFSGHyperbolicTailDisjoint.tailMap.comp e.toLinearMap = tailLinear n q := rfl
  simpa only [← Submodule.map_comp, hcomp] using ht

end SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedTail
