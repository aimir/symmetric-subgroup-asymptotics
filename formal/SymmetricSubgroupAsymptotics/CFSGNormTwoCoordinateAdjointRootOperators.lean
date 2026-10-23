import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalMixedWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSingleRootAdjoint
import SymmetricSubgroupAsymptotics.CFSGQuadraticOperatorTripleProduct

/-! Actual adjoint operators on the SAME generated Geck Lie subtype.
Root cubes, cross-second terms and the cubic product are proved from
the original lattice degrees. The half square is rational divided-power
notation; no third-factorial inversion or source faithfulness is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjointRootOperators

/-- The literal degree-three operator identity, kept abstract while
elaborating a concrete generated-Lie subtype. -/
def operatorTripleIdentity {B : Type*} [Ring B] [Algebra ℚ B] (T : Fin 3→B) (t : ℚ) : Prop :=
  CFSGQuadraticTripleProduct.value (T 0) ((1/2:ℚ) • (T 0)^2) t*
    CFSGQuadraticTripleProduct.value (T 1) ((1/2:ℚ) • (T 1)^2) t*
    CFSGQuadraticTripleProduct.value (T 2) ((1/2:ℚ) • (T 2)^2) t=
    1+t • (T 0+T 1+T 2)+
      t^2 • ((1/2:ℚ) • (T 0)^2+(1/2:ℚ) • (T 1)^2+(1/2:ℚ) • (T 2)^2+
        T 0*T 1+T 0*T 2+T 1*T 2)+t^3 • (T 0*T 1*T 2)

theorem operatorTripleIdentity_of_conditions {B : Type*} [Ring B] [Algebra ℚ B]
    (T : Fin 3→B) (hcomm : ∀i j : Fin 3,i≠j→Commute (T i) (T j))
    (hmixed : ∀i j : Fin 3,i≠j→(T i)^2*T j=0) (t : ℚ) : operatorTripleIdentity T t :=
  CFSGQuadraticOperatorTripleProduct.product_three T hcomm hmixed t

open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGNormTwoCoordinateOrthogonalMixedWord
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

def rootAdjoint (X : Mat) (hX : X∈L) : Module.End ℚ L :=
  LieAlgebra.ad ℚ L (⟨X,hX⟩ : L)

theorem rootAdjoint_cube (a : Roots A) (X : Mat) (hX : X∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) : (rootAdjoint A hd hs hp ho X hX)^3=0 := by
  apply LinearMap.ext
  intro M
  apply Subtype.ext
  change ⁅X,⁅X,⁅X,M.val⁆⁆⁆=0
  exact CFSGNormTwoCoordinateSingleRootAdjoint.single_root_ad_cube
    A hd hs hp ho a X hX hXa M.val M.property

theorem rootAdjoints_commute (a b : Roots A) (hab : integerPairing A a.val b.val=0)
    (X Y : Mat) (hX : X∈L) (hY : Y∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (hYb : Supported ell (fun v=>v+b.val) Y) :
    Commute (rootAdjoint A hd hs hp ho X hX) (rootAdjoint A hd hs hp ho Y hY) := by
  have hzero : ⁅(⟨X,hX⟩ : L),(⟨Y,hY⟩ : L)⁆=0 :=
    Subtype.ext (orthogonal_lie_zero A hd hs hp ho a b hab X Y hX hY hXa hYb)
  have hh := (LieAlgebra.ad ℚ L).map_lie (⟨X,hX⟩ : L) (⟨Y,hY⟩ : L)
  rw [hzero,map_zero] at hh
  exact sub_eq_zero.mp hh.symm

theorem rootAdjoints_mixed_zero (a b : Roots A) (hab : integerPairing A a.val b.val=0)
    (X Y : Mat) (hX : X∈L) (hY : Y∈L)
    (hXa : Supported ell (fun v=>v+a.val) X) (hYb : Supported ell (fun v=>v+b.val) Y) :
    (rootAdjoint A hd hs hp ho X hX)^2*rootAdjoint A hd hs hp ho Y hY=0 := by
  apply LinearMap.ext
  intro M
  apply Subtype.ext
  change ⁅X,⁅X,⁅Y,M.val⁆⁆⁆=0
  exact mixed_ad_zero A hd hs hp ho a b hab X Y hX hY hXa hYb M.val M.property

theorem actual_triple_operator_product (a : Fin 3→Roots A)
    (horth : ∀i j : Fin 3,i≠j→integerPairing A (a i).val (a j).val=0)
    (X : Fin 3→Mat) (hX : ∀i,X i∈L)
    (hXa : ∀i,Supported ell (fun v=>v+(a i).val) (X i)) (t : ℚ) :
    operatorTripleIdentity (fun i=>rootAdjoint A hd hs hp ho (X i) (hX i)) t := by
  let T : Fin 3→Module.End ℚ L := fun i=>rootAdjoint A hd hs hp ho (X i) (hX i)
  have hc : ∀i j : Fin 3,i≠j→Commute (T i) (T j) := by
    intro i j hij
    exact rootAdjoints_commute A hd hs hp ho (a i) (a j) (horth i j hij)
      (X i) (X j) (hX i) (hX j) (hXa i) (hXa j)
  have hm : ∀i j : Fin 3,i≠j→(T i)^2*T j=0 := by
    intro i j hij
    exact rootAdjoints_mixed_zero A hd hs hp ho (a i) (a j) (horth i j hij)
      (X i) (X j) (hX i) (hX j) (hXa i) (hXa j)
  exact operatorTripleIdentity_of_conditions T hc hm t

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjointRootOperators
