import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedTriangular
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieMixedDegree

/-! A mixed-sign lattice degree vanishes inside the SAME generated
rational Geck Lie algebra. The positive and negative coordinate-cone
supports are proved from the original coordinate simple roots, then used
with the genuine triangular decomposition. No Lie faithfulness premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedMixedDegree
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeLatticeDegree CFSGNormTwoGeckRationalAdjointStrings
open CFSGGradedMatrixSupport CFSGGradedMatrixLieMixedDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

omit [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
private theorem simple_coordinate_nonneg (i t : Fin r) :
    0≤(s₀ i:Roots A).val t := by
  change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) t
  simp only [Pi.single_apply]
  split_ifs <;> omega

private theorem positive_generator_nondecreasing (i t : Fin r) :
    Nondecreasing (fun j=>ell j t) (RootPairing.GeckConstruction.e (s₀ i)) := by
  change Nondecreasing (fun j=>ell j t) (E b₀ s₀ i)
  rw [←rational_E_eq A hs hp b₀ s₀ i]
  exact coordinate_nondecreasing_of_supported ell (s₀ i:Roots A).val _
    (field_E_lattice_support A hs hp b₀ s₀ ℚ i) t
    (simple_coordinate_nonneg A hd hs hp ho i t)

private theorem negative_generator_nondecreasing (i t : Fin r) :
    Nondecreasing (fun j=> -(ell j t)) (RootPairing.GeckConstruction.f (s₀ i)) := by
  intro j k hjk
  apply rational_F_lattice_support A hs hp b₀ (s₀ i) j k
  intro he
  have ht := congrFun he t
  change ell j t=ell k t-(s₀ i:Roots A).val t at ht
  change -(ell j t)< -(ell k t) at hjk
  have hnonneg := simple_coordinate_nonneg A hd hs hp ho i t
  omega

private theorem cartan_span_isDiag {H : Mat}
    (hH : H∈Submodule.span ℚ (Set.range (fun i : (b₀).support=>RootPairing.GeckConstruction.h i))) :
    H.IsDiag := by
  induction hH using Submodule.span_induction with
  | mem M hm=>
    obtain ⟨i,rfl⟩ := hm
    change (RootPairing.GeckConstruction.h i).IsDiag
    rw [RootPairing.GeckConstruction.h_eq_diagonal]
    exact Matrix.isDiag_diagonal _
  | zero=>exact Matrix.isDiag_zero
  | add M N _ _ hm hn=>exact hm.add hn
  | smul a M _ hm=>exact Matrix.IsDiag.smul a hm

theorem mixed_degree_zero (M : Mat) (d : Fin r→ℤ)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+d) M)
    (a b : Fin r) (ha : 0<d a) (hb : d b<0) : M=0 := by
  obtain ⟨H,hH,F,hF,E,hE,hsum⟩ :=
    CFSGNormTwoGeckGeneratedTriangular.matrix_decomposition A hd hs hp b₀ M hM
  apply CFSGGradedMatrixLieMixedDegree.mixed_degree_zero ell d H F E M a b
    (cartan_span_isDiag A hd hs hp ho hH) _ _ hsum hdeg ha hb
  · apply nondecreasing_lieSpan (fun j=> -(ell j a))
      (Set.range (fun i : (b₀).support=>RootPairing.GeckConstruction.f i)) _ hF
    rintro N ⟨i,rfl⟩
    obtain ⟨j,rfl⟩ := (s₀).surjective i
    exact negative_generator_nondecreasing A hd hs hp ho j a
  · apply nondecreasing_lieSpan (fun j=>ell j b)
      (Set.range (fun i : (b₀).support=>RootPairing.GeckConstruction.e i)) _ hE
    rintro N ⟨i,rfl⟩
    obtain ⟨j,rfl⟩ := (s₀).surjective i
    exact positive_generator_nondecreasing A hd hs hp ho j b

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedMixedDegree
