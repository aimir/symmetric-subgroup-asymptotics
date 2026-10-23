import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairRootRealization
import SymmetricSubgroupAsymptotics.CFSGTwistedDIntrinsicRootProduct
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearCompanion
import SymmetricSubgroupAsymptotics.CFSGLinearPairActionProduct

/-! Actual adjacent fixed-field singular root planes supply commuting
nonidentity elements in their SAME relative root lines whose product
is an actual relative root. All pair parameters and realizing words
remain over the actual fixed field, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAdjacentRootProducts
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticAction CFSGTwistedDPlaneRootLine
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedDRootPlaneImage
open CFSGTwistedDFixedPairRootRealization CFSGTwistedDIntrinsicRootProduct
open CFSGTwistedA2FixedField CFSGAlternatingPairOperator

private theorem conjugate_highest_ne_one (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) : g * highestRoot s q 1 * g⁻¹ ≠ 1 := by
  intro he
  have hh : highestRoot s q 1 = 1 := by
    calc
      highestRoot s q 1 = g⁻¹ * (g * highestRoot s q 1 * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := congrArg (fun z => g⁻¹ * z * g) he
      _ = 1 := by group
  exact one_ne_zero (highestRoot_injective s q (hh.trans (highestRoot_zero s q).symm))

theorem adjacent_planes_have_root_product (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hne : conjugateRootPlane s q g ≠ conjugateRootPlane s q h)
    (hmeet : (conjugateRootPlane s q g ⊓ conjugateRootPlane s q h :
      Submodule (fixedField q) (fixedSpace (s + 2) q)) ≠ ⊥)
    (hs : ∀ z ∈ conjugateRootPlane s q g ⊔ conjugateRootPlane s q h,
      fixedQuadraticForm (s + 2) q z = 0) :
    ∃ x ∈ conjugateRootLine s q g, x ≠ 1 ∧
      ∃ y ∈ conjugateRootLine s q h, y ≠ 1 ∧ Commute x y ∧
        IsRootElement s q (x * y) := by
  letI : Module.Finite (fixedField q) (fixedSpace (s + 2) q) := Module.Finite.of_finite
  let P := conjugateRootPlane s q g
  let Q := conjugateRootPlane s q h
  let B := (fixedQuadraticForm (s + 2) q).polarBilin
  have hPdim : Module.finrank (fixedField q) P = 2 := conjugateRootPlane_finrank s q g
  have hQdim : Module.finrank (fixedField q) Q = 2 := conjugateRootPlane_finrank s q h
  have hsB (x : fixedSpace (s + 2) q) (hx : x ∈ P ⊔ Q)
      (y : fixedSpace (s + 2) q) (hy : y ∈ P ⊔ Q) : B x y = 0 := by
    change fixedQuadraticForm (s + 2) q (x + y) - fixedQuadraticForm (s + 2) q x -
      fixedQuadraticForm (s + 2) q y = 0
    rw [hs _ ((P ⊔ Q).add_mem hx hy), hs _ hx, hs _ hy]
    ring
  have hPin : P ≤ P ⊔ Q := le_sup_left
  have hQin : Q ≤ P ⊔ Q := le_sup_right
  obtain ⟨u, huPQ, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  have huP : u ∈ P := huPQ.1
  have huQ : u ∈ Q := huPQ.2
  obtain ⟨v, hvP, hnv, hvspan⟩ := CFSGTwoDimensionalLinearBasis.exists_companion
    P hPdim u huP hu
  obtain ⟨w, hwQ, hnw, hwspan⟩ := CFSGTwoDimensionalLinearBasis.exists_companion
    Q hQdim u huQ hu
  have huS : u ∈ P ⊔ Q := hPin huP
  have hvS : v ∈ P ⊔ Q := hPin hvP
  have hwS : w ∈ P ⊔ Q := hQin hwQ
  have hvwS : v + w ∈ P ⊔ Q := (P ⊔ Q).add_mem hvS hwS
  have hnvw (c : fixedField q) : v + w ≠ c • u := by
    intro he
    have hew : w = c • u - v := by rw [← he]; abel
    have hwP : w ∈ P := by
      rw [hew]
      exact P.sub_mem (P.smul_mem c huP) hvP
    have hQP : Q ≤ P := by
      rw [← hwspan]
      apply Submodule.span_le.mpr
      rintro z (hz | hz)
      · rcases hz with rfl
        exact huP
      · rcases hz with rfl
        exact hwP
    exact hne (Submodule.eq_of_le_of_finrank_le hQP
      (by rw [hPdim, hQdim])).symm
  obtain ⟨a, haP, ha⟩ := exists_root_pair_action s q u v hu
    (hs _ huS) (hs _ hvS) (hsB u huS v hvS) hnv
  obtain ⟨b, hbQ, hb⟩ := exists_root_pair_action s q u w hu
    (hs _ huS) (hs _ hwS) (hsB u huS w hwS) hnw
  obtain ⟨c, _, hc⟩ := exists_root_pair_action s q u (v + w) hu
    (hs _ huS) (hs _ hvwS) (hsB u huS (v + w) hvwS) hnvw
  let x := a * highestRoot s q 1 * a⁻¹
  let y := b * highestRoot s q 1 * b⁻¹
  let z := c * highestRoot s q 1 * c⁻¹
  have hx (t : fixedSpace (s + 2) q) :
      fixedLinearHom (s + 2) q x t = t + pairOperator B u v t := by
    simpa only [one_smul] using ha 1 t
  have hy (t : fixedSpace (s + 2) q) :
      fixedLinearHom (s + 2) q y t = t + pairOperator B u w t := by
    simpa only [one_smul] using hb 1 t
  have hz (t : fixedSpace (s + 2) q) :
      fixedLinearHom (s + 2) q z t = t + pairOperator B u (v + w) t := by
    simpa only [one_smul] using hc 1 t
  have hAC : (pairOperator B u v).comp (pairOperator B u w) = 0 :=
    pairOperator_comp_eq_zero_of_orthogonal B u v w
      (hsB u huS u huS) (hsB v hvS u huS) (hsB u huS w hwS) (hsB v hvS w hwS)
  have hCA : (pairOperator B u w).comp (pairOperator B u v) = 0 :=
    pairOperator_comp_eq_zero_of_orthogonal B u w v
      (hsB u huS u huS) (hsB w hwS u huS) (hsB u huS v hvS) (hsB w hwS v hvS)
  have hxy : x * y = z := CFSGLinearPairActionProduct.mul_eq_of_pair_actions
    (fixedLinearHom (s + 2) q) (fixedLinearHom_injective (s + 2) q) B u v w x y z hx hy hz hAC
  have hyx : y * x = z := CFSGLinearPairActionProduct.mul_eq_of_pair_actions
    (fixedLinearHom (s + 2) q) (fixedLinearHom_injective (s + 2) q) B u w v y x z hy hx
      (fun t => by simpa only [add_comm w v] using hz t) hCA
  have hxL : x ∈ conjugateRootLine s q g := by
    rw [← conjugateRootLine_eq_of_plane_eq s q a g (haP.trans hvspan)]
    exact (mem_conjugateRootLine_iff s q a x).mpr ⟨1, rfl⟩
  have hyL : y ∈ conjugateRootLine s q h := by
    rw [← conjugateRootLine_eq_of_plane_eq s q b h (hbQ.trans hwspan)]
    exact (mem_conjugateRootLine_iff s q b y).mpr ⟨1, rfl⟩
  refine ⟨x, hxL, conjugate_highest_ne_one s q a,
    y, hyL, conjugate_highest_ne_one s q b, ?_, ?_⟩
  · change x * y = y * x
    exact hxy.trans hyx.symm
  · rw [hxy]
    exact ⟨c, 1, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDAdjacentRootProducts
