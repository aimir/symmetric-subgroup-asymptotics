import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalAdjoint

/-! The adjoint cube of a single actual norm-two root-degree element
vanishes on the SAME generated rational Geck Lie algebra. Homogeneous
spanning discharges the statement for every generated element; this is
not a cube-zero assertion about the ambient matrix algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSingleRootAdjoint
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

private theorem homogeneous_cube_zero (a : Roots A) (X M : Mat) (hX : X∈L) (hM : M∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (d : Fin r→ℤ)
    (hMd : Supported ell (fun v=>v+d) M) : ⁅X,⁅X,⁅X,M⁆⁆⁆=0 := by
  by_cases hzero : M=0
  · simp only [hzero,lie_zero]
  have hnorm : 4 ≤ integerPairing A (d+(3:ℤ) • a.val) (d+(3:ℤ) • a.val) := by
    rcases nonzero_homogeneous_norm_zero_or_two A hd hs hp ho M d hM hMd hzero with hc|hc
    · have hd0 := (norm_eq_zero_iff A hp d).mp hc
      subst d
      rw [zero_add,triple_root_norm A a]
      norm_num
    · exact root_plus_triple_norm_ge_four A hs hp (⟨d,hc⟩ : Roots A) a
  apply supported_eq_zero_of_norm_ge_four A hd hs hp ho _ (d+(3:ℤ) • a.val)
    ((L).lie_mem hX ((L).lie_mem hX ((L).lie_mem hX hM))) _ hnorm
  apply supported_congr (supported_lie ell a.val (a.val+(a.val+d)) X _ hXa
    (supported_lie ell a.val (a.val+d) X _ hXa (supported_lie ell a.val d X M hXa hMd)))
  intro v
  module

theorem single_root_ad_cube (a : Roots A) (X : Mat) (hX : X∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (M : Mat) (hM : M∈L) :
    ⁅X,⁅X,⁅X,M⁆⁆⁆=0 := by
  let T : Module.End ℚ Mat := LieAlgebra.ad ℚ Mat X
  have hspan : M∈homogeneousHull ell L := by
    rw [←CFSGNormTwoGeckHomogeneousSpan.lieAlgebra_eq_homogeneousHull A hs hp b₀]
    exact hM
  clear hM
  have hz : (T^3) M=0 := by
    induction hspan using Submodule.span_induction with
    | mem N hN=>
      obtain ⟨hNL,d,hNd⟩ := hN
      exact homogeneous_cube_zero A hd hs hp ho a X N hX hNL hXa d hNd
    | zero=>exact map_zero _
    | add N P _ _ hN hP=>rw [map_add,hN,hP,add_zero]
    | smul c N _ hN=>rw [map_smul,hN,smul_zero]
  exact hz

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSingleRootAdjoint
