import SymmetricSubgroupAsymptotics.CFSGE6GenerationLatticePilot
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharacterDiagonal
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble

/-! The selected E6 torus and Coxeter word are actual words in the
original integral matrix group. Their four scaling coefficients are
proved from the checked six-coordinate lattice computation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationTorusPilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGE6GenerationLatticePilot
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckCharacterDiagonal CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckDiagonalTorus
open CFSGNormTwoGeckBorelEnvelope
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev Index := E6Base.support⊕Roots CartanMatrix.E₆
abbrev e6Data := realizationData CartanMatrix.E₆ CartanMatrix.E₆_transpose
  E6_positive_definite E6Base E6Index
abbrev Ambient (K : Type) [Field K] := (Matrix Index Index K)ˣ

def root (K : Type) [Field K] (i : Fin 6) (a : K) : Ambient K :=
  canonicalRoot e6Data K false i a

def coxeter (K : Type) [Field K] : Ambient K :=
  wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index K coxeterWord

def torus (K : Type) [Field K] (g : Kˣ) : Ambient K :=
  characterDiagonal CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base K torusFunctional g

theorem torus_eq_word (K : Type) [Field K] (g : Kˣ) : torus K g=
    parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K 4 g*
    parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K 5 g := by
  apply Units.ext
  simp only [torus,characterDiagonal,CFSGDiagonalMatrixUnits.diagonalHom_val,
    Units.val_mul,torus_diagonal,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  cases j with
  | inl j=>simp only [latticeWeight,map_zero,weight,zpow_zero,Units.val_one,one_mul]
  | inr j=>
    change ((g^(integerPairing CartanMatrix.E₆
      ((Pi.single 4 1 : Fin 6→ℤ)+Pi.single 5 1) j.val):Kˣ):K)=
        (g:K)^(integerPairing CartanMatrix.E₆ (Pi.single 4 1) j.val)*
        (g:K)^(integerPairing CartanMatrix.E₆ (Pi.single 5 1) j.val)
    simp only [map_add,LinearMap.add_apply,zpow_add,Units.val_mul,
      Units.val_zpow_eq_zpow_val]

theorem root_mem_canonical (K : Type) [Field K] (i : Fin 6) (a : K) :
    root K i a∈canonicalElementaryGroup e6Data K :=
  (canonicalElementaryRoot e6Data K false i a).property

theorem torus_mem_canonical (K : Type) [Field K] (g : Kˣ) :
    torus K g∈canonicalElementaryGroup e6Data K := by
  rw [torus_eq_word]
  apply (canonicalElementaryGroup e6Data K).mul_mem
  · exact (canonicalElementaryGroup e6Data K).mul_mem
      (parameterWeyl_mem CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K 4 g)
      ((canonicalElementaryGroup e6Data K).inv_mem
        (parameterWeyl_mem CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index K 4 1))
  · exact (canonicalElementaryGroup e6Data K).mul_mem
      (parameterWeyl_mem CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K 5 g)
      ((canonicalElementaryGroup e6Data K).inv_mem
        (parameterWeyl_mem CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index K 5 1))

theorem coxeter_mem_canonical (K : Type) [Field K] :
    coxeter K∈canonicalElementaryGroup e6Data K := by
  exact CFSGNormTwoCoordinateNormalizerSoluble.wordUnit_mem_canonical
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K coxeterWord

theorem torus_fixes_zero (K : Type) [Field K] (g : Kˣ) (a : K) :
    torus K g*root K 0 a*(torus K g)⁻¹=root K 0 a := by
  have hh := character_conjugate_positive CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K torusFunctional g 0 a
  change torus K g*root K 0 a*(torus K g)⁻¹=
    root K 0 (a*(g:K)^(torusFunctional (Pi.single 0 1))) at hh
  simpa only [functional_zero,zpow_zero,mul_one] using hh

theorem torus_scales_five (K : Type) [Field K] (g : Kˣ) (a : K) :
    torus K g*root K 5 a*(torus K g)⁻¹=root K 5 ((g:K)*a) := by
  have hh := character_conjugate_positive CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K torusFunctional g 5 a
  change torus K g*root K 5 a*(torus K g)⁻¹=
    root K 5 (a*(g:K)^(torusFunctional (Pi.single 5 1))) at hh
  simpa only [functional_five,zpow_one,mul_comm] using hh

theorem conjugated_torus_eq_character (K : Type) [Field K] (g : Kˣ) :
    coxeter K*torus K g*(coxeter K)⁻¹=
      characterDiagonal CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base K (torusFunctional.comp coxeterLinear.symm.toLinearMap) g :=
  word_conjugate_character CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K torusFunctional g coxeterWord

theorem conjugated_torus_scales_zero (K : Type) [Field K] (g : Kˣ) (a : K) :
    (coxeter K*torus K g*(coxeter K)⁻¹)*root K 0 a*
      (coxeter K*torus K g*(coxeter K)⁻¹)⁻¹=root K 0 ((g:K)⁻¹*a) := by
  rw [conjugated_torus_eq_character]
  have hh := character_conjugate_positive CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K
    (torusFunctional.comp coxeterLinear.symm.toLinearMap) g 0 a
  change _=root K 0 (a*(g:K)^(torusFunctional (coxeterLinear.symm (Pi.single 0 1)))) at hh
  simpa only [pullback_zero,zpow_neg_one,mul_comm] using hh

theorem conjugated_torus_scales_five (K : Type) [Field K] (g : Kˣ) (a : K) :
    (coxeter K*torus K g*(coxeter K)⁻¹)*root K 5 a*
      (coxeter K*torus K g*(coxeter K)⁻¹)⁻¹=root K 5 ((g:K)*a) := by
  rw [conjugated_torus_eq_character]
  have hh := character_conjugate_positive CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K
    (torusFunctional.comp coxeterLinear.symm.toLinearMap) g 5 a
  change _=root K 5 (a*(g:K)^(torusFunctional (coxeterLinear.symm (Pi.single 5 1)))) at hh
  simpa only [pullback_five,zpow_one,mul_comm] using hh

theorem conjugated_torus_commutes (K : Type) [Field K] (g : Kˣ) :
    Commute (coxeter K*torus K g*(coxeter K)⁻¹) (torus K g) := by
  rw [conjugated_torus_eq_character]
  change Commute
    (CFSGDiagonalMatrixUnits.diagonalHom Index K _)
    (CFSGDiagonalMatrixUnits.diagonalHom Index K _)
  exact (Commute.all _ _).map (CFSGDiagonalMatrixUnits.diagonalHom Index K)

end SymmetricSubgroupAsymptotics.CFSGE6GenerationTorusPilot
