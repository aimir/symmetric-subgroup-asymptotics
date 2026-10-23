import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalAdjoint

/-! Each actual mixed three-letter adjoint word in two orthogonal
root degrees vanishes on the SAME generated rational Geck Lie algebra.
This is stronger than cancellation in a summed adjoint cube and supplies
the cross-second coefficients of literal root-operator products. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalMixedWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
open CFSGGradedMatrixHomogeneousLieSpan CFSGNormTwoCoordinateHomogeneousDegrees
open CFSGNormTwoOrthogonalOrbitNorms CFSGNormTwoCoordinateOrthogonalAdjoint
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

theorem orthogonal_lie_zero (a b : Roots A) (hab : integerPairing A a.val b.val=0)
    (X Y : Mat) (hX : X∈L) (hY : Y∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (hYb : Supported ell (fun v=>v+b.val) Y) :
    ⁅X,Y⁆=0 := by
  apply supported_eq_zero_of_norm_ge_four A hd hs hp ho _ (a.val+b.val)
    ((L).lie_mem hX hY) (supported_lie ell a.val b.val X Y hXa hYb)
  rw [norm_add A hs,a.property,b.property,hab]
  norm_num

theorem orthogonal_ad_commute (a b : Roots A) (hab : integerPairing A a.val b.val=0)
    (X Y : Mat) (hX : X∈L) (hY : Y∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (hYb : Supported ell (fun v=>v+b.val) Y) :
    Commute (LieAlgebra.ad ℚ Mat X) (LieAlgebra.ad ℚ Mat Y) := by
  have hz := orthogonal_lie_zero A hd hs hp ho a b hab X Y hX hY hXa hYb
  have hh := (LieAlgebra.ad ℚ Mat).map_lie X Y
  rw [hz,map_zero] at hh
  exact sub_eq_zero.mp hh.symm

private theorem homogeneous_mixed_zero (a b : Roots A) (hab : integerPairing A a.val b.val=0)
    (X Y M : Mat) (hX : X∈L) (hY : Y∈L) (hM : M∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (hYb : Supported ell (fun v=>v+b.val) Y)
    (d : Fin r→ℤ) (hMd : Supported ell (fun v=>v+d) M) : ⁅X,⁅X,⁅Y,M⁆⁆⁆=0 := by
  by_cases hzero : M=0
  · simp only [hzero,lie_zero]
  have hnorm : 4 ≤ integerPairing A (d+((2:ℤ) • a.val+b.val))
      (d+((2:ℤ) • a.val+b.val)) := by
    rcases nonzero_homogeneous_norm_zero_or_two A hd hs hp ho M d hM hMd hzero with hc|hc
    · have hd0 := (norm_eq_zero_iff A hp d).mp hc
      subst d
      rw [zero_add,double_orthogonal_norm A hs a b hab]
      norm_num
    · exact root_plus_double_orthogonal_norm_ge_four A hs hp (⟨d,hc⟩ : Roots A) a b hab
  apply supported_eq_zero_of_norm_ge_four A hd hs hp ho _ (d+((2:ℤ) • a.val+b.val))
    ((L).lie_mem hX ((L).lie_mem hX ((L).lie_mem hY hM))) _ hnorm
  apply supported_congr (supported_lie ell a.val (a.val+(b.val+d)) X _ hXa
    (supported_lie ell a.val (b.val+d) X _ hXa (supported_lie ell b.val d Y M hYb hMd)))
  intro v
  simp only [two_smul]
  abel

theorem mixed_ad_zero (a b : Roots A) (hab : integerPairing A a.val b.val=0)
    (X Y : Mat) (hX : X∈L) (hY : Y∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (hYb : Supported ell (fun v=>v+b.val) Y)
    (M : Mat) (hM : M∈L) : ⁅X,⁅X,⁅Y,M⁆⁆⁆=0 := by
  let T : Module.End ℚ Mat := LieAlgebra.ad ℚ Mat X*LieAlgebra.ad ℚ Mat X*LieAlgebra.ad ℚ Mat Y
  have hspan : M∈homogeneousHull ell L := by
    rw [←CFSGNormTwoGeckHomogeneousSpan.lieAlgebra_eq_homogeneousHull A hs hp b₀]
    exact hM
  clear hM
  have hz : T M=0 := by
    induction hspan using Submodule.span_induction with
    | mem N hN=>
      obtain ⟨hNL,d,hNd⟩ := hN
      exact homogeneous_mixed_zero A hd hs hp ho a b hab X Y N hX hY hNL hXa hYb d hNd
    | zero=>exact map_zero _
    | add N P _ _ hN hP=>rw [map_add,hN,hP,add_zero]
    | smul c N _ hN=>rw [map_smul,hN,smul_zero]
  exact hz

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalMixedWord
