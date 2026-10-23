import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedTail
import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalCrossPairing

/-! A single actual relative-root word aligns BOTH members of every
disjoint maximal singular pair. The induction retains the same fixed
tail, its exact dimension, and its disjointness. No independent frame
choices are silently identified, and the anisotropic rank-two base is
handled by its actual one-dimensional singular spaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPairAlignment
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedTailLinear CFSGTwistedDSingularTailDimension
open CFSGTwistedDSingularDimensionBound CFSGTwistedDAllRankFixedPairFrame
open CFSGTwistedDOpposedTail CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeTailEmbedding CFSGTwistedDMaximalSpaceOrbit
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDPositiveSpaceCoordinates
open CFSGTwistedDNegativeSpaceCoordinates CFSGTwistedA2FixedField
open CFSGQuadraticMaximalSingularGallery

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem maximal_of_full_rank (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q))
    (hs : ∀ v ∈ P, fixedQuadraticForm n q v = 0)
    (hd : Module.finrank (fixedField q) P = n + 1) : MaximalSingular (fixedQuadraticForm n q) P := by
  refine ⟨hs, ?_⟩
  intro T hT hle
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [hd]
  exact singular_finrank_le q n T hT

theorem exists_first_frame (n : ℕ) (q : CFSG.PrimePower)
    (P R : Submodule (fixedField q) (fixedSpace n q))
    (hP : MaximalSingular (fixedQuadraticForm n q) P)
    (hR : MaximalSingular (fixedQuadraticForm n q) R) (hdis : Disjoint P R) :
    ∃ g : relativeRootGroup n q,
      firstAxis n q ∈ P.map (fixedLinearHom n q g).toLinearMap ∧
      negativeFirst n q ∈ R.map (fixedLinearHom n q g).toLinearMap := by
  have hdim := maximalSingular_finrank n q P hP
  have hPbot : P ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
  obtain ⟨w, hw, hwQ, hB⟩ := CFSGQuadraticMaximalCrossPairing.opposed_pairing_one
    (fixedQuadraticForm n q) P R hP hR hdis u hu hu0
  obtain ⟨g, hgu, hgw⟩ := exists_fixed_pair_frame n q u w hu0 (hP.1 u hu) hwQ hB
  exact ⟨g, ⟨u, hu, hgu⟩, ⟨w, hw, hgw⟩⟩

theorem positiveHead_fixed_action (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace (n + 1) q) :
    positiveHead n q (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v) =
      positiveHead n q v := by
  apply Subtype.ext
  exact head_positive n q g v.val

theorem negative_of_head_tail (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hh : positiveHead n q v = 0)
    (ht : tailLinear n q v ∈ negativeSpace n q) : v ∈ negativeSpace (n + 1) q := by
  rw [mem_negativeSpace_iff] at ht ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg (fun a : fixedField q => (a : q.Extension 2)) hh
  · exact ht j

theorem exists_align_full_rank (n : ℕ) (q : CFSG.PrimePower)
    (P R : Submodule (fixedField q) (fixedSpace n q))
    (hP : ∀ v ∈ P, fixedQuadraticForm n q v = 0)
    (hR : ∀ v ∈ R, fixedQuadraticForm n q v = 0)
    (hdP : Module.finrank (fixedField q) P = n + 1)
    (hdR : Module.finrank (fixedField q) R = n + 1) (hdis : Disjoint P R) :
    ∃ g : relativeRootGroup n q,
      P.map (fixedLinearHom n q g).toLinearMap = positiveSpace n q ∧
      R.map (fixedLinearHom n q g).toLinearMap = negativeSpace n q := by
  induction n with
  | zero =>
    obtain ⟨g, he, hf⟩ := exists_first_frame 0 q P R
      (maximal_of_full_rank 0 q P hP hdP) (maximal_of_full_rank 0 q R hR hdR) hdis
    let A := P.map (fixedLinearHom 0 q g).toLinearMap
    let B := R.map (fixedLinearHom 0 q g).toLinearMap
    have hA : Module.finrank (fixedField q) A = 1 :=
      ((fixedLinearHom 0 q g).finrank_map_eq P).trans hdP
    have hB : Module.finrank (fixedField q) B = 1 :=
      ((fixedLinearHom 0 q g).finrank_map_eq R).trans hdR
    have hlineA : Submodule.span (fixedField q) {firstAxis 0 q} = A :=
      Submodule.eq_of_le_of_finrank_le
        ((Submodule.span_singleton_le_iff_mem _ _).mpr he)
        (by rw [hA, finrank_span_singleton (firstAxis_nonzero 0 q)])
    have hlineB : Submodule.span (fixedField q) {negativeFirst 0 q} = B :=
      Submodule.eq_of_le_of_finrank_le
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hf)
        (by rw [hB, finrank_span_singleton (negativeFirst_nonzero 0 q)])
    have hepos : firstAxis 0 q ∈ positiveSpace 0 q := by
      rw [mem_positiveSpace_iff]
      intro i
      change (Pi.single (Sum.inl (0 : Fin 2)) (1 : q.Extension 2) :
        CFSGOrthogonalDSerreMatrices.Index 2 → q.Extension 2) (Sum.inr i) = 0
      simp only [Pi.single_apply, Sum.inr_ne_inl, if_false]
    have hAP : A ≤ positiveSpace 0 q := by
      rw [← hlineA]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hepos
    have hBN : B ≤ negativeSpace 0 q := by
      rw [← hlineB]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr (negativeFirst_mem 0 q)
    exact ⟨g, Submodule.eq_of_le_of_finrank_le hAP (by rw [positiveSpace_finrank, hA]),
      Submodule.eq_of_le_of_finrank_le hBN (by rw [negativeSpace_finrank, hB])⟩
  | succ n ih =>
    obtain ⟨g, he, hf⟩ := exists_first_frame (n + 1) q P R
      (maximal_of_full_rank (n + 1) q P hP hdP)
      (maximal_of_full_rank (n + 1) q R hR hdR) hdis
    let L := fixedLinearHom (n + 1) q g
    let A := P.map L.toLinearMap
    let B := R.map L.toLinearMap
    have hAs : ∀ v ∈ A, fixedQuadraticForm (n + 1) q v = 0 := by
      rintro v ⟨u, hu, rfl⟩
      exact (fixedLinearHom_preserves_Q (n + 1) q g u).trans (hP u hu)
    have hBs : ∀ v ∈ B, fixedQuadraticForm (n + 1) q v = 0 := by
      rintro v ⟨u, hu, rfl⟩
      exact (fixedLinearHom_preserves_Q (n + 1) q g u).trans (hR u hu)
    have hA : Module.finrank (fixedField q) A = n + 2 := (L.finrank_map_eq P).trans hdP
    have hB : Module.finrank (fixedField q) B = n + 2 := (L.finrank_map_eq R).trans hdR
    have hAB : Disjoint A B := Submodule.disjoint_map (f := L.toLinearMap) L.injective hdis
    let T := A.map (tailLinear n q)
    let U := B.map (tailLinear n q)
    have hT : Module.finrank (fixedField q) T = n + 1 := by
      have hd := tail_finrank n q A hAs he
      change Module.finrank (fixedField q) T + 1 = Module.finrank (fixedField q) A at hd
      omega
    have hU : Module.finrank (fixedField q) U = n + 1 := by
      have hd := negative_tail_finrank n q B hBs hf
      change Module.finrank (fixedField q) U + 1 = Module.finrank (fixedField q) B at hd
      omega
    obtain ⟨h, hhP, hhR⟩ := ih T U (tail_singular n q A hAs he)
      (negative_tail_singular n q B hBs hf) hT hU (disjoint_tails n q A B hAs hBs he hf hAB)
    let t := tailRelativeHom n q h
    have hAP : A.map (fixedLinearHom (n + 1) q t).toLinearMap ≤ positiveSpace (n + 1) q := by
      rintro v ⟨x, hx, rfl⟩
      apply positive_of_head_tail n q
      · change negativeHead n q (fixedLinearHom (n + 1) q (tailRelativeHom n q h) x) = 0
        rw [negativeHead_fixed_action]
        exact negativeHead_zero n q A hAs he x hx
      · change tailLinear n q (fixedLinearHom (n + 1) q (tailRelativeHom n q h) x) ∈ positiveSpace n q
        rw [tail_fixed_action]
        rw [← hhP]
        exact ⟨tailLinear n q x, ⟨x, hx, rfl⟩, rfl⟩
    have hBN : B.map (fixedLinearHom (n + 1) q t).toLinearMap ≤ negativeSpace (n + 1) q := by
      rintro v ⟨x, hx, rfl⟩
      apply negative_of_head_tail n q
      · change positiveHead n q (fixedLinearHom (n + 1) q (tailRelativeHom n q h) x) = 0
        rw [positiveHead_fixed_action]
        exact positiveHead_zero n q B hBs hf x hx
      · change tailLinear n q (fixedLinearHom (n + 1) q (tailRelativeHom n q h) x) ∈ negativeSpace n q
        rw [tail_fixed_action]
        rw [← hhR]
        exact ⟨tailLinear n q x, ⟨x, hx, rfl⟩, rfl⟩
    have hAPeq : A.map (fixedLinearHom (n + 1) q t).toLinearMap = positiveSpace (n + 1) q :=
      Submodule.eq_of_le_of_finrank_le hAP (by
        rw [positiveSpace_finrank, (fixedLinearHom (n + 1) q t).finrank_map_eq, hA])
    have hBNeq : B.map (fixedLinearHom (n + 1) q t).toLinearMap = negativeSpace (n + 1) q :=
      Submodule.eq_of_le_of_finrank_le hBN (by
        rw [negativeSpace_finrank, (fixedLinearHom (n + 1) q t).finrank_map_eq, hB])
    have hcomp : (fixedLinearHom (n + 1) q (t * g)).toLinearMap =
        (fixedLinearHom (n + 1) q t).toLinearMap.comp L.toLinearMap := by
      rw [map_mul]
      rfl
    refine ⟨t * g, ?_, ?_⟩
    · rw [hcomp, Submodule.map_comp]
      exact hAPeq
    · rw [hcomp, Submodule.map_comp]
      exact hBNeq

theorem exists_align_maximal (n : ℕ) (q : CFSG.PrimePower)
    (P R : Submodule (fixedField q) (fixedSpace n q))
    (hP : MaximalSingular (fixedQuadraticForm n q) P)
    (hR : MaximalSingular (fixedQuadraticForm n q) R) (hdis : Disjoint P R) :
    ∃ g : relativeRootGroup n q,
      P.map (fixedLinearHom n q g).toLinearMap = positiveSpace n q ∧
      R.map (fixedLinearHom n q g).toLinearMap = negativeSpace n q :=
  exists_align_full_rank n q P R hP.1 hR.1
    (maximalSingular_finrank n q P hP) (maximalSingular_finrank n q R hR) hdis

end SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPairAlignment
