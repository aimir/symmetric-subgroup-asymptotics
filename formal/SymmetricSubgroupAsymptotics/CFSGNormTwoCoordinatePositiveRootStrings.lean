import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordString
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNonrootDegreeZero
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString

/-! Length-two strings for an ACTUAL arbitrary positive lattice root and
a simple root of pairing -1. The two extra bracket degrees have norm six;
their vanishing is proved inside the SAME generated Geck Lie algebra.
No ambient-matrix root-space recognition premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootStrings
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoCoordinateRootWordString
open CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "ell" => latticeWeight A hs hp b₀

private theorem simple_nonnegative (i j : Fin r) : 0≤(s₀ i:Roots A).val j := by
  change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) j
  simp only [Pi.single_apply]
  split_ifs <;> omega

theorem raising_twice_zero (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ⁅fieldRoot D ℚ false i,⁅fieldRoot D ℚ false i,selectedCoefficient A hd hs hp ho k⁆⁆=0 := by
  let a : Fin r→ℤ := (s₀ i:Roots A).val
  let X := selectedCoefficient A hd hs hp ho k
  let E := fieldRoot D ℚ false i
  have hEmem : E∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
    change fieldRoot D ℚ false i∈RootPairing.GeckConstruction.lieAlgebra b₀
    rw [rational_E_eq]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (s₀ i)
  have hXmem : X∈RootPairing.GeckConstruction.lieAlgebra b₀ :=
    selectedCoefficient_mem A hd hs hp ho k
  have hEdeg : Supported ell (fun v=>v+a) E := field_E_lattice_support A hs hp b₀ s₀ ℚ i
  have hXdeg : Supported ell (fun v=>v+k.val) X := selectedCoefficient_degree A hd hs hp ho k
  apply CFSGNormTwoCoordinateNonrootDegreeZero.nonnegative_norm_four_or_six_degree_zero
    A hd hs hp ho _ (a+(a+k.val))
    ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hEmem
      ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hEmem hXmem))
    (supported_lie ell a (a+k.val) _ _ hEdeg (supported_lie ell a k.val _ _ hEdeg hXdeg))
  · intro j
    change 0≤a j+(a j+k.val j)
    have ha : 0≤a j := simple_nonnegative A hd hs hp ho i j
    exact add_nonneg ha (add_nonneg ha (hk j))
  · right
    have ha : integerPairing A a a=2 := (s₀ i:Roots A).property
    have hab : integerPairing A a k.val= -1 :=
      (integer_symmetric A hs a k.val).trans hpair
    have hba : integerPairing A k.val a= -1 := hpair
    simp only [map_add,LinearMap.add_apply,ha,k.property,hba,hab] <;> norm_num

theorem root_commutes_with_raising (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    Commute (selectedCoefficient A hd hs hp ho k)
      ⁅fieldRoot D ℚ false i,selectedCoefficient A hd hs hp ho k⁆ := by
  let a : Fin r→ℤ := (s₀ i:Roots A).val
  let X := selectedCoefficient A hd hs hp ho k
  let E := fieldRoot D ℚ false i
  have hEmem : E∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
    change fieldRoot D ℚ false i∈RootPairing.GeckConstruction.lieAlgebra b₀
    rw [rational_E_eq]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (s₀ i)
  have hXmem : X∈RootPairing.GeckConstruction.lieAlgebra b₀ :=
    selectedCoefficient_mem A hd hs hp ho k
  have hEdeg : Supported ell (fun v=>v+a) E := field_E_lattice_support A hs hp b₀ s₀ ℚ i
  have hXdeg : Supported ell (fun v=>v+k.val) X := selectedCoefficient_degree A hd hs hp ho k
  have hz : ⁅X,⁅E,X⁆⁆=0 := by
    apply CFSGNormTwoCoordinateNonrootDegreeZero.nonnegative_norm_four_or_six_degree_zero
      A hd hs hp ho _ (k.val+(a+k.val))
      ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hXmem
        ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hEmem hXmem))
      (supported_lie ell k.val (a+k.val) _ _ hXdeg (supported_lie ell a k.val _ _ hEdeg hXdeg))
    · intro j
      change 0≤k.val j+(a j+k.val j)
      exact add_nonneg (hk j) (add_nonneg (simple_nonnegative A hd hs hp ho i j) (hk j))
    · right
      have ha : integerPairing A a a=2 := (s₀ i:Roots A).property
      have hab : integerPairing A a k.val= -1 :=
        (integer_symmetric A hs a k.val).trans hpair
      have hba : integerPairing A k.val a= -1 := hpair
      simp only [map_add,LinearMap.add_apply,ha,k.property,hba,hab] <;> norm_num
  exact sub_eq_zero.mp hz

theorem root_conjugation (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) (t : ℚ) :
    (canonicalRoot D ℚ false i t : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)*
      selectedCoefficient A hd hs hp ho k*
      (((canonicalRoot D ℚ false i t)⁻¹ :
        (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)ˣ) :
        Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)=
      selectedCoefficient A hd hs hp ho k+
        t • ⁅fieldRoot D ℚ false i,selectedCoefficient A hd hs hp ho k⁆ :=
  canonicalRoot_conjugation_of_double_lie D false i _
    (raising_twice_zero A hd hs hp ho k hk i hpair) t

theorem root_weyl_conjugation (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    (canonicalWeyl D ℚ i : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)*
      selectedCoefficient A hd hs hp ho k*
      (((canonicalWeyl D ℚ i)⁻¹ :
        (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)ˣ) :
        Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)=
      ⁅fieldRoot D ℚ false i,selectedCoefficient A hd hs hp ho k⁆ := by
  apply CFSGSerreQuadraticAdjointWeylString.weyl_on_pair D i
    (selectedCoefficient A hd hs hp ho k) _ rfl
    (raising_twice_zero A hd hs hp ho k hk i hpair)
    (CFSGNormTwoCoordinateRootString.lower_root_bracket_zero A hd hs hp ho k hk i hpair _
      (selectedCoefficient_mem A hd hs hp ho k) (selectedCoefficient_degree A hd hs hp ho k))
    (selected_lowering_after_raising A hd hs hp ho k hk i hpair)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootStrings
