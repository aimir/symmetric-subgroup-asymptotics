import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveCentralizer
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Abel

/-! Coefficient-one sparse products generate the positive D chain and
paired directions. These are universal matrix identities, not a finite
root-system census or an assumed unipotent presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveDirectionProducts
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDIndexPositiveCentralizer
variable (K : Type) [Field K] (r : ℕ)

theorem chain_chain (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    chainMatrix K r i j * chainMatrix K r j k - chainMatrix K r j k * chainMatrix K r i j =
      chainMatrix K r i k := by
  simp [chainMatrix, sub_mul, mul_sub, hij, hjk, hik, Ne.symm hij, Ne.symm hjk, Ne.symm hik]

theorem chain_pair_first (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    chainMatrix K r i j * pairedUpper K j k - pairedUpper K j k * chainMatrix K r i j =
      pairedUpper K i k := by
  simp [chainMatrix, pairedUpper, sub_mul, mul_sub, hij, hjk, hik,
    Ne.symm hij, Ne.symm hjk, Ne.symm hik]

theorem chain_pair_second (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    chainMatrix K r j k * pairedUpper K i k - pairedUpper K i k * chainMatrix K r j k =
      pairedUpper K i j := by
  simp [chainMatrix, pairedUpper, sub_mul, mul_sub, hij, hjk, hik,
    Ne.symm hij, Ne.symm hjk, Ne.symm hik]
  abel

theorem commutes_bracket {B : Type*} [Ring B] (A E F : B)
    (hE : A * E = E * A) (hF : A * F = F * A) :
    A * (E * F - F * E) = (E * F - F * E) * A :=
  (Commute.sub_right (Commute.mul_right hE hF) (Commute.mul_right hF hE)).eq

end SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveDirectionProducts
