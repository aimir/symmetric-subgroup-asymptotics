import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedTriangular
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieTriangularLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! Inside the SAME generated rational Geck Lie algebra, the lattice
degree of a negative simple root is its actual one-dimensional generator
line. Triangular decomposition and the height-one filtration discharge
membership in the generator span before the degree projection is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedSimpleLine
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckNegativeLatticeDegree CFSGGradedMatrixSupport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "w" => weight A hs hp b₀ coordinateHeight
local notation "ell" => latticeWeight A hs hp b₀

omit [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
private theorem weight_lattice (j : (b₀).support⊕Roots A) : w j=coordinateHeight (ell j) := by
  cases j <;> simp only [weight,latticeWeight,map_zero]

private theorem cartan_span_isDiag {H : Mat}
    (hH : H∈Submodule.span ℚ (Set.range (fun i : (b₀).support=>RootPairing.GeckConstruction.h i))) :
    H.IsDiag := by
  induction hH using Submodule.span_induction with
  | mem N hn=>
    obtain ⟨i,rfl⟩ := hn
    change (RootPairing.GeckConstruction.h i : Mat).IsDiag
    rw [RootPairing.GeckConstruction.h_eq_diagonal]
    exact Matrix.isDiag_diagonal _
  | zero=>exact Matrix.isDiag_zero
  | add N P _ _ hn hp=>exact hn.add hp
  | smul a N _ hn=>exact Matrix.IsDiag.smul a hn

omit [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
private theorem negative_height_support (i : (b₀).support) :
    Supported (fun j=> -w j) (fun h=>h+1) (RootPairing.GeckConstruction.f i) := by
  intro j k hne
  apply rational_F_lattice_support A hs hp b₀ i j k
  intro he
  apply hne
  change -w j= -w k+1
  change ell j=ell k-(i:Roots A).val at he
  rw [weight_lattice,weight_lattice]
  have hh := congrArg coordinateHeight he
  rw [map_sub,simple_height A hd hs hp ho i] at hh
  omega

include ho in
theorem negative_simple_line (i : (b₀).support) (M : Mat)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v-(i:Roots A).val) M) :
    ∃c : ℚ,M=c • RootPairing.GeckConstruction.f i := by
  obtain ⟨H,hH,F,hF,E,hE,hsum⟩ :=
    CFSGNormTwoGeckGeneratedTriangular.matrix_decomposition A hd hs hp b₀ M hM
  have hheight : Supported (fun j=> -w j) (fun h=>h+1) M := by
    intro j k hne
    apply hdeg j k
    intro he
    apply hne
    change -w j= -w k+1
    change ell j=ell k-(i:Roots A).val at he
    rw [weight_lattice,weight_lattice]
    have hh := congrArg coordinateHeight he
    rw [map_sub,simple_height A hd hs hp ho i] at hh
    omega
  have hspan : M∈Submodule.span ℚ
      (Set.range (fun j : (b₀).support=>RootPairing.GeckConstruction.f j)) := by
    apply CFSGGradedMatrixLieTriangularLayer.negative_layer_mem_span w
      (Set.range (fun j : (b₀).support=>RootPairing.GeckConstruction.f j))
      (Set.range (fun j : (b₀).support=>RootPairing.GeckConstruction.e j))
      _ _ H F E M (cartan_span_isDiag A hd hs hp ho hH) hF hE hsum hheight
    · rintro N ⟨j,rfl⟩
      exact negative_height_support A hd hs hp ho j
    · rintro N ⟨j,rfl⟩
      exact rational_E_support A hs hp b₀ coordinateHeight (simple_height A hd hs hp ho) j
  have hd' : Function.Injective (fun j : (b₀).support=> -(j:Roots A).val) := by
    intro j k hjk
    exact Subtype.ext (Subtype.ext (neg_injective hjk))
  have hline : M∈Submodule.span ℚ ({RootPairing.GeckConstruction.f i} : Set Mat) := by
    have hX : ∀j : (b₀).support,Supported ell
        (fun v=>v+ -(j:Roots A).val) (RootPairing.GeckConstruction.f j) := by
      intro j
      simpa only [sub_eq_add_neg] using rational_F_lattice_support A hs hp b₀ j
    exact CFSGGradedMatrixSingleDegreeSpan.mem_single_line_of_mem_span ell
      (fun j : (b₀).support=> -(j:Roots A).val) hd'
      (fun j : (b₀).support=>RootPairing.GeckConstruction.f j) hX i M hspan
      (by simpa only [sub_eq_add_neg] using hdeg)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hline
  exact ⟨c,hc.symm⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedSimpleLine
