import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
import SymmetricSubgroupAsymptotics.CFSGIntegralCubicRootOperators

/-! Literal signed G2 simple-root units in the SAME folded D4 group.
Their coefficients are the actual base changes of the ORIGINAL G2
cubic realization data, uniformly over every commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRootUnits
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckIntegralCoefficients
open CFSGGTwoD4GeckIntegralRealization CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityFixedWeylWords CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortOrbitCommutator
open CFSGNormTwoGeckTripleRootPolynomial
open CFSGSerreQuadraticMatrix (fieldRoot fieldSecond map_fieldRoot canonicalRoot canonicalRoot_val canonicalRoot_inverse)
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

private theorem map_rawSecond {r : ℕ} {B : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : CFSGSerreQuadraticMatrix.Data B I)
    (K : Type) [CommRing K] (neg : Bool) (i : Fin r) :
    (Int.castRingHom K).mapMatrix (fieldSecond D ℤ neg i)=fieldSecond D K neg i := by
  ext a b
  simp [fieldSecond]

theorem fieldRoot_eq (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) :
    CFSGSerreCubicMatrix.fieldRoot realizationData K neg i=
      if i=0 then tripleFirst A hs hp Base Index K neg outerNode else fieldRoot rawData K neg 1 := by
  change (Int.castRingHom K).mapMatrix
    (integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i))=_
  rw [integerGenerator_root]
  unfold integerRoot
  split_ifs
  · simp only [tripleFirst,map_add,map_fieldRoot]
  · exact map_fieldRoot rawData (Int.castRingHom K) neg 1

theorem fieldSecond_eq (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) :
    CFSGSerreCubicMatrix.fieldSecond realizationData K neg i=
      if i=0 then tripleSecond A hs hp Base Index K neg outerNode else fieldSecond rawData K neg 1 := by
  change (Int.castRingHom K).mapMatrix (integerSecond neg i)=_
  unfold integerSecond
  split_ifs
  · simp only [tripleSecond,map_add,map_mul,map_fieldRoot,map_rawSecond]
  · exact map_rawSecond rawData K neg 1

theorem fieldThird_eq (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) :
    CFSGSerreCubicMatrix.fieldThird realizationData K neg i=
      if i=0 then tripleThird A hs hp Base Index K neg outerNode else 0 := by
  change (Int.castRingHom K).mapMatrix (integerThird neg i)=_
  unfold integerThird
  split_ifs
  · simp only [tripleThird,map_mul,map_fieldRoot]
  · exact map_zero _

def rootUnit (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) (t : K) :
    (Matrix CFSGGTwoD4GeckGenerators.GeckIndex CFSGGTwoD4GeckGenerators.GeckIndex K)ˣ :=
  if i=0 then shortOrbit K (RingEquiv.refl K) neg t else canonicalRoot rawData K neg 1 t

theorem rootUnit_val (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) (t : K) :
    (rootUnit K neg i t : Matrix CFSGGTwoD4GeckGenerators.GeckIndex CFSGGTwoD4GeckGenerators.GeckIndex K)=
      CFSGIntegralCubicRootOperators.exponential K
        (CFSGSerreCubicMatrix.fieldRoot realizationData K neg i)
        (CFSGSerreCubicMatrix.fieldSecond realizationData K neg i)
        (CFSGSerreCubicMatrix.fieldThird realizationData K neg i) t := by
  fin_cases i
  · change (shortOrbit K (RingEquiv.refl K) neg t : Matrix _ _ K)=
      CFSGIntegralCubicRootOperators.exponential K
        (CFSGSerreCubicMatrix.fieldRoot realizationData K neg 0)
        (CFSGSerreCubicMatrix.fieldSecond realizationData K neg 0)
        (CFSGSerreCubicMatrix.fieldThird realizationData K neg 0) t
    rw [fieldRoot_eq,fieldSecond_eq,fieldThird_eq]
    simpa only [CFSGIntegralCubicRootOperators.exponential,if_pos rfl] using
      canonicalRootTriple_val A hs hp Base Index K neg outerNode outer_orthogonal t
  · change (canonicalRoot rawData K neg 1 t : Matrix _ _ K)=
      CFSGIntegralCubicRootOperators.exponential K
        (CFSGSerreCubicMatrix.fieldRoot realizationData K neg 1)
        (CFSGSerreCubicMatrix.fieldSecond realizationData K neg 1)
        (CFSGSerreCubicMatrix.fieldThird realizationData K neg 1) t
    rw [fieldRoot_eq,fieldSecond_eq,fieldThird_eq]
    simp only [show (1:Fin 2)≠0 by decide,if_false,
      CFSGIntegralCubicRootOperators.exponential,smul_zero,add_zero,canonicalRoot_val]

theorem rootUnit_inverse (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) (t : K) :
    (rootUnit K neg i t)⁻¹=rootUnit K neg i (-t) := by
  fin_cases i
  · exact (shortOrbit_inverse K (RingEquiv.refl K) neg t).symm
  · exact canonicalRoot_inverse rawData K neg 1 t

theorem rootUnit_inv_val (K : Type) [CommRing K] (neg : Bool) (i : Fin 2) (t : K) :
    (↑((rootUnit K neg i t)⁻¹) : Matrix CFSGGTwoD4GeckGenerators.GeckIndex CFSGGTwoD4GeckGenerators.GeckIndex K)=
      CFSGIntegralCubicRootOperators.exponential K
        (CFSGSerreCubicMatrix.fieldRoot realizationData K neg i)
        (CFSGSerreCubicMatrix.fieldSecond realizationData K neg i)
        (CFSGSerreCubicMatrix.fieldThird realizationData K neg i) (-t) := by
  rw [rootUnit_inverse,rootUnit_val]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRootUnits
