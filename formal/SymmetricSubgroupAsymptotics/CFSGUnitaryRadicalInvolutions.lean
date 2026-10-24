import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryClearingParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing

/-! In characteristic two, an actual radical involution has singular
vector parameter. Consequently a subgroup with trivial central
intersection has a quadratically singular quotient image. Polar
isotropy alone is not used to infer this stronger condition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryParameters
open CFSGTwistedAUnitaryColumnClearing

private theorem double_eq_zero (q : CFSG.PrimePower) (h2 : (2 : q.Extension 2) = 0)
    (b : q.Extension 2) : b + b = 0 := by
  calc
    _ = (2 : q.Extension 2) * b := by ring
    _ = 0 := by rw [h2, zero_mul]

private theorem upperUnit_involution_dot_zero
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (w v : I → K) (b : K) (h2 : (2 : K) = 0)
    (h : upperUnit w v b * upperUnit w v b = 1) : dotProduct w v = 0 := by
  rw [upperUnit_mul] at h
  have hz := congrArg (fun u : (Matrix (Index I) (Index I) K)ˣ =>
    (u : Matrix (Index I) (Index I) K) (.inl ()) (.inr (.inr ()))) h
  change b + b + dotProduct w v = 0 at hz
  have hb : b + b = 0 := by
    calc
      _ = (2 : K) * b := by ring
      _ = 0 := by rw [h2, zero_mul]
  simpa only [hb, zero_add] using hz

private theorem norm_zero_of_radicalRow_dot_zero
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (σ : K ≃+* K) (eps : K) (H : Matrix I I K) (v : I → K)
    (heps : eps ≠ 0) (h : dotProduct (radicalRow σ eps H v) v = 0) :
    hermitianNorm σ H v = 0 := by
  rw [radicalRow_dotProduct] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr heps)

private theorem middle_norm_zero_iff (q : CFSG.PrimePower) (t : ℕ)
    (v : Fin (t + 1) → q.Extension 2) :
    hermitianNorm (definingFieldAutomorphism q 2) (middleForm q t) v = 0 ↔
      unitaryNaturalPair q t v v = 0 := by
  change dotProduct (fun i => definingFieldAutomorphism q 2 (v i))
      ((-(signedReversalUnit (q.Extension 2) t : Mat (q.Extension 2) t)) *ᵥ v) = 0 ↔
    dotProduct (fun i => definingFieldAutomorphism q 2 (v i))
      ((signedReversalUnit (q.Extension 2) t : Mat (q.Extension 2) t) *ᵥ v) = 0
  rw [Matrix.neg_mulVec, dotProduct_neg, neg_eq_zero]

theorem fixedRadical_involution_parameter_singular (q : CFSG.PrimePower) (t : ℕ)
    (h2 : (2 : q.Extension 2) = 0) (g : fixedRadical q t) (hg : g * g = 1) :
    unitaryNaturalPair q t (fixedRadicalParameterHom q t g).toAdd
      (fixedRadicalParameterHom q t g).toAdd = 0 := by
  obtain ⟨b, hb⟩ := fixedRadical_block_shape q t g
  have he : blockFixedMatrixHom q t g.val * blockFixedMatrixHom q t g.val = 1 := by
    have hh := congrArg (fun u : fixedRadical q t => blockFixedMatrixHom q t u.val) hg
    change blockFixedMatrixHom q t (g.val * g.val) = blockFixedMatrixHom q t 1 at hh
    simpa only [map_mul, map_one] using hh
  rw [hb] at he
  have hz := upperUnit_involution_dot_zero
    (firstRow q t (fixedRadicalParameterHom q t g).toAdd)
    (fixedRadicalParameterHom q t g).toAdd b h2 he
  have hp : parity q t ≠ 0 :=
    pow_ne_zero t (neg_ne_zero.mpr (one_ne_zero : (1 : q.Extension 2) ≠ 0))
  have hn := norm_zero_of_radicalRow_dot_zero (definingFieldAutomorphism q 2)
    (parity q t) (middleForm q t) (fixedRadicalParameterHom q t g).toAdd hp hz
  exact (middle_norm_zero_iff q t _).mp hn

theorem radicalTrivialCentralIntersection_image_singular (q : CFSG.PrimePower) (t : ℕ)
    (h2 : (2 : q.Extension 2) = 0) (J : Subgroup (fixedRadical q t))
    (hC : J.comap (centralRadicalHom q t) = ⊥)
    (v : Multiplicative (Fin (t + 1) → q.Extension 2))
    (hv : v ∈ J.map (fixedRadicalParameterHom q t)) :
    unitaryNaturalPair q t v.toAdd v.toAdd = 0 := by
  obtain ⟨g, hg, rfl⟩ := hv
  have hk : g * g ∈ (fixedRadicalParameterHom q t).ker := by
    change fixedRadicalParameterHom q t (g * g) = 1
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    change (fixedRadicalParameterHom q t g).toAdd +
      (fixedRadicalParameterHom q t g).toAdd = 0
    funext i
    exact double_eq_zero q h2 _
  rw [← centralRadicalHom_range_eq_kernel] at hk
  obtain ⟨c, hc⟩ := hk
  have hcJ : c ∈ J.comap (centralRadicalHom q t) := by
    change centralRadicalHom q t c ∈ J
    rw [hc]
    exact J.mul_mem hg hg
  rw [hC] at hcJ
  have hc1 : c = 1 := Subgroup.mem_bot.mp hcJ
  have hs : g * g = 1 := by rw [← hc, hc1, map_one]
  exact fixedRadical_involution_parameter_singular q t h2 g hs

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
