import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
import SymmetricSubgroupAsymptotics.CFSGQuadraticParameterizedCollecting

/-! Actual arbitrary-positive-root collecting against a simple root.
The result is a literal Weyl-conjugate root word, at two independent
rational parameters. All string and nilpotence hypotheses are discharged
inside the original generated Geck algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRationalRootCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateRootWordString
open CFSGNormTwoCoordinatePositiveRootStrings CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho

theorem simple_positive_collecting (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) (t a : ℚ) :
    canonicalRoot D ℚ false i t*selectedRootElement A hd hs hp ho ℚ k a*
      (canonicalRoot D ℚ false i t)⁻¹*(selectedRootElement A hd hs hp ho ℚ k a)⁻¹=
      canonicalWeyl D ℚ i*selectedRootElement A hd hs hp ho ℚ k (a*t)*
        (canonicalWeyl D ℚ i)⁻¹ := by
  let X : Mat := selectedCoefficient A hd hs hp ho k
  let Y : Mat := ⁅fieldRoot D ℚ false i,X⁆
  have hword := CFSGQuadraticParameterizedCollecting.conjugate_scaled_difference
    (canonicalRoot D ℚ false i t) (canonicalWeyl D ℚ i) X Y
    (root_commutes_with_raising A hd hs hp ho k hk i hpair)
    (selectedCoefficient_cube A hd hs hp ho k) t a
    (root_conjugation A hd hs hp ho k hk i hpair t)
    (root_weyl_conjugation A hd hs hp ho k hk i hpair)
  apply Units.ext
  simp only [Units.val_mul,selectedRootElement_inverse,selectedRootElement_val_rational]
  exact hword

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRationalRootCollecting
