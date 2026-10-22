import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootBracketTransport
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates

/-! Actual selected coefficients in DISTINCT original integer root
degrees are independent over EVERY field. Literal lattice-degree
projections and primitive nonzero word coefficients provide the proof;
no characteristic-p weight-character separation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckNegativeWordCoefficients
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootBracketTransport
open CFSGGradedMatrixSupport CFSGGradedMatrixDistinctDegreeCoordinates
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

theorem selectedFieldCoefficient_support (K : Type) [Field K] (k : Roots A) :
    Supported ell (fun v=>v+k.val) (selectedFieldCoefficient A hd hs hp ho K k) := by
  rw [selectedFieldCoefficient_eq_first]
  let p := rootWitness A hd hs hp ho k
  apply supported_congr (first_support A hs hp b₀ s₀ K p.val.1 p.val.2)
  intro v
  exact congrArg (fun d : Fin r→ℤ=>v+d) p.property.symm

theorem root_family_coefficients_unique {J : Type*} [Fintype J] [DecidableEq J]
    (K : Type) [Field K] (f : J→Roots A) (hf : Function.Injective f) (c d : J→K)
    (h : (∑i,c i • selectedFieldCoefficient A hd hs hp ho K (f i))=
      ∑i,d i • selectedFieldCoefficient A hd hs hp ho K (f i)) : c=d := by
  have hinj : Function.Injective (fun i : J=>(f i).val) := by
    intro i j hij
    exact hf (Subtype.ext hij)
  exact coefficients_unique ell (fun i : J=>(f i).val) hinj
    (fun i=>selectedFieldCoefficient A hd hs hp ho K (f i))
    (fun i=>selectedFieldCoefficient_support A hd hs hp ho K (f i))
    (fun i=>selectedFieldCoefficient_ne_zero A hd hs hp ho K (f i)) c d h

theorem all_root_coefficients_unique (K : Type) [Field K] (c d : Roots A→K)
    (h : (∑i,c i • selectedFieldCoefficient A hd hs hp ho K i)=
      ∑i,d i • selectedFieldCoefficient A hd hs hp ho K i) : c=d :=
  root_family_coefficients_unique A hd hs hp ho K id Function.injective_id c d h

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCoefficientCoordinates
