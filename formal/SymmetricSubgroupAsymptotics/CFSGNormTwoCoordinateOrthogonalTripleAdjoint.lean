import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalAdjoint
import SymmetricSubgroupAsymptotics.CFSGFiniteEndomorphismWords
import SymmetricSubgroupAsymptotics.CFSGThreeLetterWordDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalTripleNorms

/-! An actual orthogonal triple has adjoint fourth power zero on the
SAME generated rational Geck Lie algebra. Operator words retain original
lattice degrees; the proof uses integer counts rather than an expanded
eighty-one-term matrix identity. No triality-model identification is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTripleAdjoint
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
open CFSGGradedMatrixHomogeneousLieSpan CFSGNormTwoCoordinateHomogeneousDegrees
open CFSGFiniteEndomorphismWords CFSGThreeLetterWordDegree CFSGNormTwoOrthogonalTripleNorms
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
local notation "L" => RootPairing.GeckConstruction.lieAlgebra b₀

omit [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
private theorem ad_word_mem (X : Fin 3→Mat) (hX : ∀i,X i∈L)
    (w : List (Fin 3)) (M : Mat) (hM : M∈L) :
    applyWord (fun i=>LieAlgebra.ad ℚ Mat (X i)) w M∈L := by
  induction w with
  | nil=>exact hM
  | cons i w ih=>exact (L).lie_mem (hX i) ih

omit [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
private theorem ad_word_supported (a : Fin 3→Roots A) (X : Fin 3→Mat)
    (hXa : ∀i,Supported ell (fun v=>v+(a i).val) (X i))
    (w : List (Fin 3)) (M : Mat) (d : Fin r→ℤ)
    (hMd : Supported ell (fun v=>v+d) M) :
    Supported ell (fun v=>v+(d+(w.map (fun i=>(a i).val)).sum))
      (applyWord (fun i=>LieAlgebra.ad ℚ Mat (X i)) w M) := by
  induction w with
  | nil=>simpa only [List.map_nil,List.sum_nil,add_zero] using hMd
  | cons i w ih=>
    apply supported_congr (supported_lie ell (a i).val
      (d+(w.map (fun j=>(a j).val)).sum) (X i) _ (hXa i) ih)
    intro v
    simp only [List.map_cons,List.sum_cons]
    abel

private theorem four_letter_word_zero (a : Fin 3→Roots A)
    (h01 : integerPairing A (a 0).val (a 1).val=0)
    (h02 : integerPairing A (a 0).val (a 2).val=0)
    (h12 : integerPairing A (a 1).val (a 2).val=0)
    (X : Fin 3→Mat) (hX : ∀i,X i∈L)
    (hXa : ∀i,Supported ell (fun v=>v+(a i).val) (X i))
    (w : List (Fin 3)) (hw : w.length=4) (M : Mat) (hM : M∈L)
    (d : Fin r→ℤ) (hMd : Supported ell (fun v=>v+d) M) :
    applyWord (fun i=>LieAlgebra.ad ℚ Mat (X i)) w M=0 := by
  by_cases hzero : M=0
  · subst M
    have hz : ∀v : List (Fin 3),applyWord (fun i=>LieAlgebra.ad ℚ Mat (X i)) v (0 : Mat)=0 := by
      intro v
      induction v with
      | nil=>rfl
      | cons i v ih=>
        change LieAlgebra.ad ℚ Mat (X i) (applyWord (fun j=>LieAlgebra.ad ℚ Mat (X j)) v 0)=0
        rw [ih,map_zero]
    exact hz w
  let x : ℤ := w.count 0
  let y : ℤ := w.count 1
  let z : ℤ := w.count 2
  have hx : 0≤x := Int.natCast_nonneg _
  have hy : 0≤y := Int.natCast_nonneg _
  have hz : 0≤z := Int.natCast_nonneg _
  have hsum : x+y+z=4 := by
    have hc : w.count 0+w.count 1+w.count 2=4 := (count_sum_eq_length w).trans hw
    change (w.count 0:ℤ)+(w.count 1:ℤ)+(w.count 2:ℤ)=4
    exact_mod_cast hc
  have hword : (w.map (fun i=>(a i).val)).sum=x • (a 0).val+y • (a 1).val+z • (a 2).val :=
    sum_eq_count_smul (fun i=>(a i).val) w
  have hnorm : 4 ≤ integerPairing A (d+(w.map (fun i=>(a i).val)).sum)
      (d+(w.map (fun i=>(a i).val)).sum) := by
    rcases nonzero_homogeneous_norm_zero_or_two A hd hs hp ho M d hM hMd hzero with hc|hc
    · have hd0 := (norm_eq_zero_iff A hp d).mp hc
      subst d
      rw [zero_add,hword]
      have hh := four_steps_norm_ge_twelve A hs (a 0) (a 1) (a 2)
        h01 h02 h12 x y z hx hy hz hsum
      omega
    · rw [hword]
      have hh := root_four_steps_norm_ge_six A hs hp (⟨d,hc⟩ : Roots A)
        (a 0) (a 1) (a 2) h01 h02 h12 x y z hx hy hz hsum
      dsimp only at hh
      omega
  exact CFSGNormTwoCoordinateOrthogonalAdjoint.supported_eq_zero_of_norm_ge_four
    A hd hs hp ho _ _ (ad_word_mem A hd hs hp ho X hX w M hM)
    (ad_word_supported A hd hs hp ho a X hXa w M d hMd) hnorm

theorem orthogonal_three_ad_four (a : Fin 3→Roots A)
    (h01 : integerPairing A (a 0).val (a 1).val=0)
    (h02 : integerPairing A (a 0).val (a 2).val=0)
    (h12 : integerPairing A (a 1).val (a 2).val=0)
    (X : Fin 3→Mat) (hX : ∀i,X i∈L)
    (hXa : ∀i,Supported ell (fun v=>v+(a i).val) (X i))
    (M : Mat) (hM : M∈L) :
    (LieAlgebra.ad ℚ Mat (∑i,X i)^4) M=0 := by
  rw [map_sum]
  let T : Module.End ℚ Mat := ∑i,LieAlgebra.ad ℚ Mat (X i)
  have hspan : M∈homogeneousHull ell L := by
    rw [←CFSGNormTwoGeckHomogeneousSpan.lieAlgebra_eq_homogeneousHull A hs hp b₀]
    exact hM
  clear hM
  have hz : (T^4) M=0 := by
    induction hspan using Submodule.span_induction with
    | mem N hN=>
      obtain ⟨hNL,d,hNd⟩ := hN
      apply sum_pow_apply_eq_zero_of_words (fun i : Fin 3=>LieAlgebra.ad ℚ Mat (X i)) 4 N
      intro w hw
      exact four_letter_word_zero A hd hs hp ho a h01 h02 h12 X hX hXa w hw N hNL d hNd
    | zero=>exact map_zero _
    | add N P _ _ hN hP=>rw [map_add,hN,hP,add_zero]
    | smul c N _ hN=>rw [map_smul,hN,smul_zero]
  exact hz

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTripleAdjoint
