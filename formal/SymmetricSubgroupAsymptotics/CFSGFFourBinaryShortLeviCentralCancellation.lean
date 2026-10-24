import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCancellingRootActions
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergCharTwoRootRange
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords

/-! The duplicate actual raised factors cancel by the characteristic-two
root-parameter law. Hence the extra paired central axes are fixed by the
short positive Levi generators, with no omitted central correction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralCancellation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGFFourBinaryShortLeviCancellingRootActions CFSGFFourBinaryCentralCoordinateWords
open CFSGFFourE6HeisenbergLeviRoots CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGExceptionalHeisenbergRootRelations
open CFSGExceptionalHeisenbergProduct CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGExceptionalHeisenbergCharTwoRootRange
local instance fFourCentralCancellationRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev param (K : Type) [CommRing K] (k : Roots A) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K k t
private abbrev py (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  yNegative A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private def node : Fin 2 → Fin 4 := ![0,1]
private def extraAxis : Fin 2 → Fin 3 := ![2,0]

private theorem result_pairing (second : Bool) (n : Fin 2) :
    integerPairing A (resultRoot second n).val.val (sourceRoot second n 1).val.val=1 := by
  cases second <;> fin_cases n <;> decide

theorem short_positive_conjugate_cancelling_pair (K : Type) [Field K] [CharP K 2]
    (second : Bool) (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        (param K (sourceRoot second n 0).val t*param K (sourceRoot second n 1).val t) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      param K (sourceRoot second n 0).val t*param K (sourceRoot second n 1).val t := by
  let g : U K := canonicalRoot realizationData K false (node n) a
  let x : U K := param K (sourceRoot second n 0).val t
  let z : U K := param K (sourceRoot second n 1).val t
  let y : U K := param K (resultRoot second n).val (a*t)
  have h0 : g*x*g⁻¹=x*y := short_positive_conjugate_cancelling_root K second n 0 a t
  have h1 : g*z*g⁻¹=z*y := short_positive_conjugate_cancelling_root K second n 1 a t
  have hc : Commute y z := CFSGNormTwoCoordinateRootPairCommute.pair_commute A hd hs hp ho K
    (resultRoot second n).val (sourceRoot second n 1).val (Or.inr (result_pairing second n)) (a*t) t
  have hyy : y*y=1 := by
    change selectedRootElement A hd hs hp ho K (resultRoot second n).val (a*t) *
      selectedRootElement A hd hs hp ho K (resultRoot second n).val (a*t) = 1
    rw [selectedRootElement_add,CharTwo.add_self_eq_zero,selectedRootElement_zero]
  change g*(x*z)*g⁻¹=x*z
  calc
    _=(g*x*g⁻¹)*(g*z*g⁻¹) := by group
    _=(x*y)*(z*y) := by rw [h0,h1]
    _=x*(y*z)*y := by group
    _=x*(z*y)*y := by rw [hc.eq]
    _=(x*z)*(y*y) := by group
    _=x*z := by rw [hyy,mul_one]

theorem short_positive_conjugate_extra_first (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single (extraAxis n) t,0))) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single (extraAxis n) t,0))) := by
  have hchart : centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single (extraAxis n) t,0))) =
      param K (sourceRoot false n 0).val t*param K (sourceRoot false n 1).val t := by
    rw [central_first_word]
    fin_cases n <;> rfl
  rw [hchart]
  exact short_positive_conjugate_cancelling_pair K false n a t

theorem short_positive_conjugate_extra_second (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single (extraAxis n) t))) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single (extraAxis n) t))) := by
  have hy (i : Fin 10) : py K i t=param K (configuration.yRoot i).val t :=
    DFunLike.congr_fun (yNegative_eq_selectedRootHom A hd hs hp ho configuration K i)
      (Multiplicative.ofAdd t)
  have hchart : centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single (extraAxis n) t))) =
      param K (sourceRoot true n 0).val t*param K (sourceRoot true n 1).val t := by
    rw [central_second_word]
    change py K (pairPick (extraAxis n)) t*py K (partner (pairPick (extraAxis n))) t = _
    rw [hy,hy]
    fin_cases n <;> rfl
  rw [hchart]
  exact short_positive_conjugate_cancelling_pair K true n a t

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralCancellation
