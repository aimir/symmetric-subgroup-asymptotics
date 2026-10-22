import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedCorrespondence
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalReversal

/-! Actual highest and opposite root units in the three-dimensional
natural elementary group. Their source lifts use the original A2 group,
and trace-skew parameters give original fixed-subgroup elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
open CFSGSerreSquareZeroMatrix CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

def entryUnit {i j : Fin 3} (hij : i ≠ j) (a : K) : (Mat K 2)ˣ :=
  Matrix.SpecialLinearGroup.toGL (elementary hij a)

theorem entryUnit_val {i j : Fin 3} (hij : i ≠ j) (a : K) :
    (entryUnit K hij a : Mat K 2) = 1 + Matrix.single i j a := rfl

theorem entryUnit_inv_val {i j : Fin 3} (hij : i ≠ j) (a : K) :
    (↑((entryUnit K hij a)⁻¹) : Mat K 2) = 1 + Matrix.single i j (-a) := by
  have h : (entryUnit K hij a)⁻¹ = entryUnit K hij (-a) := by
    unfold entryUnit
    rw [← map_inv, elementary_inv]
  rw [h, entryUnit_val]

theorem entryUnit_commutator {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : K) :
    ⁅entryUnit K hij a, entryUnit K hjk b⁆ = entryUnit K hik (a * b) := by
  exact (map_commutatorElement Matrix.SpecialLinearGroup.toGL
    (elementary hij a) (elementary hjk b)).symm.trans
      (congrArg Matrix.SpecialLinearGroup.toGL (elementary_commutator hij hjk hik a b))

theorem naturalRootUnit_positive_zero (a : K) :
    naturalRootUnit K 2 false 0 a = entryUnit K (show (0 : Fin 3) ≠ 1 by decide) a := by
  apply Units.ext
  change 1 + a • Matrix.single (0 : Fin 3) 1 1 = 1 + Matrix.single 0 1 a
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]

theorem naturalRootUnit_positive_one (a : K) :
    naturalRootUnit K 2 false 1 a = entryUnit K (show (1 : Fin 3) ≠ 2 by decide) a := by
  apply Units.ext
  change 1 + a • Matrix.single (1 : Fin 3) 2 1 = 1 + Matrix.single 1 2 a
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]

theorem naturalRootUnit_negative_zero (a : K) :
    naturalRootUnit K 2 true 0 a = entryUnit K (show (1 : Fin 3) ≠ 0 by decide) a := by
  apply Units.ext
  change 1 + a • (Matrix.single (0 : Fin 3) 1 1).transpose = 1 + Matrix.single 1 0 a
  simp only [Matrix.transpose_single, Matrix.smul_single, smul_eq_mul, mul_one]

theorem naturalRootUnit_negative_one (a : K) :
    naturalRootUnit K 2 true 1 a = entryUnit K (show (2 : Fin 3) ≠ 1 by decide) a := by
  apply Units.ext
  change 1 + a • (Matrix.single (1 : Fin 3) 2 1).transpose = 1 + Matrix.single 2 1 a
  simp only [Matrix.transpose_single, Matrix.smul_single, smul_eq_mul, mul_one]

def highest (a : K) : NaturalElementary K 2 :=
  ⁅elementaryRoot K (naturalRootUnit K 2) false 0 a,
    elementaryRoot K (naturalRootUnit K 2) false 1 1⁆

def opposite (a : K) : NaturalElementary K 2 :=
  ⁅elementaryRoot K (naturalRootUnit K 2) true 1 a,
    elementaryRoot K (naturalRootUnit K 2) true 0 1⁆

theorem highest_val (a : K) : (highest K a).val =
    entryUnit K (show (0 : Fin 3) ≠ 2 by decide) a := by
  change ⁅naturalRootUnit K 2 false 0 a, naturalRootUnit K 2 false 1 1⁆ = _
  rw [naturalRootUnit_positive_zero, naturalRootUnit_positive_one, entryUnit_commutator,
    mul_one]

theorem opposite_val (a : K) : (opposite K a).val =
    entryUnit K (show (2 : Fin 3) ≠ 0 by decide) a := by
  change ⁅naturalRootUnit K 2 true 1 a, naturalRootUnit K 2 true 0 1⁆ = _
  rw [naturalRootUnit_negative_one, naturalRootUnit_negative_zero, entryUnit_commutator,
    mul_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
