import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHomogeneousSpan
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHomogeneousDegrees
import SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalOrbitNorms
import Mathlib.Tactic.Module

/-! The adjoint cube of a sum of two orthogonal original root-degree
elements is zero on the SAME generated rational Geck Lie algebra.
Homogeneous spanning, the actual invariant form, and integer norm gaps
discharge the assertion on every generated element, not just generators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalAdjoint
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
open CFSGGradedMatrixHomogeneousLieSpan CFSGNormTwoCoordinateHomogeneousDegrees
open CFSGNormTwoOrthogonalOrbitNorms
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

theorem supported_eq_zero_of_norm_ge_four (M : Mat) (d : Fin r→ℤ)
    (hM : M∈L) (hdeg : Supported ell (fun v=>v+d) M)
    (hnorm : 4 ≤ integerPairing A d d) : M=0 := by
  by_contra hne
  have hc := nonzero_homogeneous_norm_zero_or_two A hd hs hp ho M d hM hdeg hne
  omega

private theorem triple_lie_zero (X Y Z M : Mat) (a b c d t : Fin r→ℤ)
    (hX : X∈L) (hY : Y∈L) (hZ : Z∈L) (hM : M∈L)
    (hXa : Supported ell (fun v=>v+a) X)
    (hYb : Supported ell (fun v=>v+b) Y)
    (hZc : Supported ell (fun v=>v+c) Z)
    (hMd : Supported ell (fun v=>v+d) M)
    (ht : a+b+c=t) (hnorm : 4 ≤ integerPairing A (d+t) (d+t)) :
    ⁅X,⁅Y,⁅Z,M⁆⁆⁆=0 := by
  apply supported_eq_zero_of_norm_ge_four A hd hs hp ho _ (d+t)
    ((L).lie_mem hX ((L).lie_mem hY ((L).lie_mem hZ hM))) _ hnorm
  apply supported_congr (supported_lie ell a (b+(c+d)) X _ hXa
    (supported_lie ell b (c+d) Y _ hYb (supported_lie ell c d Z M hZc hMd)))
  intro v
  rw [←ht]
  abel

private theorem homogeneous_cube_zero (a b : Roots A)
    (hab : integerPairing A a.val b.val=0) (X Y M : Mat)
    (hX : X∈L) (hY : Y∈L) (hM : M∈L)
    (hXa : Supported ell (fun v=>v+a.val) X)
    (hYb : Supported ell (fun v=>v+b.val) Y)
    (d : Fin r→ℤ) (hMd : Supported ell (fun v=>v+d) M) :
    ⁅X+Y,⁅X+Y,⁅X+Y,M⁆⁆⁆=0 := by
  by_cases hzero : M=0
  · simp only [hzero,lie_zero]
  have hc := nonzero_homogeneous_norm_zero_or_two A hd hs hp ho M d hM hMd hzero
  have hd' : d=0 ∨ integerPairing A d d=2 := by
    rcases hc with hc|hc
    · exact Or.inl ((norm_eq_zero_iff A hp d).mp hc)
    · exact Or.inr hc
  have hba : integerPairing A b.val a.val=0 := by
    rw [integer_symmetric A hs b.val a.val,hab]
  have h3a : 4 ≤ integerPairing A (d+(3:ℤ) • a.val) (d+(3:ℤ) • a.val) := by
    rcases hd' with rfl|hd'
    · rw [zero_add,triple_root_norm A a]
      norm_num
    · exact root_plus_triple_norm_ge_four A hs hp (⟨d,hd'⟩ : Roots A) a
  have h3b : 4 ≤ integerPairing A (d+(3:ℤ) • b.val) (d+(3:ℤ) • b.val) := by
    rcases hd' with rfl|hd'
    · rw [zero_add,triple_root_norm A b]
      norm_num
    · exact root_plus_triple_norm_ge_four A hs hp (⟨d,hd'⟩ : Roots A) b
  have h2a : 4 ≤ integerPairing A (d+((2:ℤ) • a.val+b.val))
      (d+((2:ℤ) • a.val+b.val)) := by
    rcases hd' with rfl|hd'
    · rw [zero_add,double_orthogonal_norm A hs a b hab]
      norm_num
    · exact root_plus_double_orthogonal_norm_ge_four A hs hp (⟨d,hd'⟩ : Roots A) a b hab
  have h2b : 4 ≤ integerPairing A (d+((2:ℤ) • b.val+a.val))
      (d+((2:ℤ) • b.val+a.val)) := by
    rcases hd' with rfl|hd'
    · rw [zero_add,double_orthogonal_norm A hs b a hba]
      norm_num
    · exact root_plus_double_orthogonal_norm_ge_four A hs hp (⟨d,hd'⟩ : Roots A) b a hba
  have hXXX := triple_lie_zero A hd hs hp ho X X X M a.val a.val a.val d
    ((3:ℤ) • a.val) hX hX hX hM hXa hXa hXa hMd (by module) h3a
  have hXXY := triple_lie_zero A hd hs hp ho X X Y M a.val a.val b.val d
    ((2:ℤ) • a.val+b.val) hX hX hY hM hXa hXa hYb hMd (by module) h2a
  have hXYX := triple_lie_zero A hd hs hp ho X Y X M a.val b.val a.val d
    ((2:ℤ) • a.val+b.val) hX hY hX hM hXa hYb hXa hMd (by module) h2a
  have hYXX := triple_lie_zero A hd hs hp ho Y X X M b.val a.val a.val d
    ((2:ℤ) • a.val+b.val) hY hX hX hM hYb hXa hXa hMd (by module) h2a
  have hXYY := triple_lie_zero A hd hs hp ho X Y Y M a.val b.val b.val d
    ((2:ℤ) • b.val+a.val) hX hY hY hM hXa hYb hYb hMd (by module) h2b
  have hYXY := triple_lie_zero A hd hs hp ho Y X Y M b.val a.val b.val d
    ((2:ℤ) • b.val+a.val) hY hX hY hM hYb hXa hYb hMd (by module) h2b
  have hYYX := triple_lie_zero A hd hs hp ho Y Y X M b.val b.val a.val d
    ((2:ℤ) • b.val+a.val) hY hY hX hM hYb hYb hXa hMd (by module) h2b
  have hYYY := triple_lie_zero A hd hs hp ho Y Y Y M b.val b.val b.val d
    ((3:ℤ) • b.val) hY hY hY hM hYb hYb hYb hMd (by module) h3b
  simp only [add_lie,lie_add,hXXX,hXXY,hXYX,hYXX,hXYY,hYXY,hYYX,hYYY,add_zero]

theorem orthogonal_ad_cube (a b : Roots A)
    (hab : integerPairing A a.val b.val=0) (X Y : Mat)
    (hX : X∈L) (hY : Y∈L)
    (hXa : Supported ell (fun v=>v+a.val) X)
    (hYb : Supported ell (fun v=>v+b.val) Y)
    (M : Mat) (hM : M∈L) : ⁅X+Y,⁅X+Y,⁅X+Y,M⁆⁆⁆=0 := by
  let T : Module.End ℚ Mat := LieAlgebra.ad ℚ Mat (X+Y)
  have hspan : M∈homogeneousHull ell L := by
    rw [←CFSGNormTwoGeckHomogeneousSpan.lieAlgebra_eq_homogeneousHull A hs hp b₀]
    exact hM
  clear hM
  have hz : (T^3) M=0 := by
    induction hspan using Submodule.span_induction with
    | mem N hN=>
      obtain ⟨hNL,d,hNd⟩ := hN
      change ⁅X+Y,⁅X+Y,⁅X+Y,N⁆⁆⁆=0
      exact homogeneous_cube_zero A hd hs hp ho a b hab X Y N hX hY hNL hXa hYb d hNd
    | zero=>exact map_zero _
    | add N P _ _ hN hP=>rw [map_add,hN,hP,add_zero]
    | smul c N _ hN=>rw [map_smul,hN,smul_zero]
  exact hz

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalAdjoint
