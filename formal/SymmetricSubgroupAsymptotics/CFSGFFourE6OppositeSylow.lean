import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionDegree
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist

/-! Literal integral Geck opposition is an automorphism of the folded
F4 matrix group and sends its ACTUAL positive Sylow onto the negative
intersection. No assertion that the opposition matrix is an inner F4
word is needed for this Sylow transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeSylow
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGFFourE6NegativeRootUnits
open CFSGFFourE6PositiveSylow CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckFieldOpposition CFSGNormTwoGeckOppositionDegree
open CFSGNormTwoGeckOppositionWeyl CFSGTwistedE6GeckPositiveTwist
open CFSGSerreQuadraticMatrix

def rawOpposition (K : Type) [Field K] : MulAut ((Matrix Index Index K)ˣ) :=
  MulAut.conj (oppositionUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K)

theorem rawOpposition_involutive (K : Type) [Field K] : Function.Involutive (rawOpposition K) := by
  intro g
  exact opposition_twice CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K g

theorem rawOpposition_root (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    rawOpposition K (canonicalRoot realizationData K neg i t) =
      canonicalRoot realizationData K (!neg) i t := by
  cases neg
  · exact folded_opposition K i t
  · have he := congrArg (rawOpposition K) (folded_opposition K i t)
    change rawOpposition K (rawOpposition K (canonicalRoot realizationData K false i t)) =
      rawOpposition K (canonicalRoot realizationData K true i t) at he
    rw [rawOpposition_involutive] at he
    exact he.symm

theorem rawOpposition_mem (K : Type) [Field K] (g : (Matrix Index Index K)ˣ)
    (hg : g∈canonicalElementaryGroup realizationData K) :
    rawOpposition K g∈canonicalElementaryGroup realizationData K := by
  have hle : canonicalElementaryGroup realizationData K ≤
      (canonicalElementaryGroup realizationData K).comap (rawOpposition K).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨neg,i,t,rfl⟩
    change rawOpposition K (canonicalRoot realizationData K neg i t)∈
      canonicalElementaryGroup realizationData K
    rw [rawOpposition_root]
    exact Subgroup.subset_closure ⟨!neg,i,t,rfl⟩
  exact hle hg

def foldedOpposition (K : Type) [Field K] :
    MulAut (canonicalElementaryGroup realizationData K) where
  toFun g := ⟨rawOpposition K g.val,rawOpposition_mem K g.val g.property⟩
  invFun g := ⟨rawOpposition K g.val,rawOpposition_mem K g.val g.property⟩
  left_inv g := by apply Subtype.ext; exact rawOpposition_involutive K g.val
  right_inv g := by apply Subtype.ext; exact rawOpposition_involutive K g.val
  map_mul' g h := by apply Subtype.ext; exact map_mul (rawOpposition K) g.val h.val

theorem foldedOpposition_involutive (K : Type) [Field K] : Function.Involutive (foldedOpposition K) := by
  intro g
  apply Subtype.ext
  exact rawOpposition_involutive K g.val

def negativeSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Sylow p (canonicalElementaryGroup realizationData K) :=
  (positiveSylow K p).mapSurjective (f:=(foldedOpposition K).toMonoidHom)
    (foldedOpposition K).surjective

theorem negativeSylow_coe (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (negativeSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) =
      (Negative K).subgroupOf (canonicalElementaryGroup realizationData K) := by
  change (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
    (foldedOpposition K).toMonoidHom = _
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hyp : y.val∈Positive K := (le_of_eq (positiveSylow_coe K p)) hy
    exact opposition_conjugate_mem CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K false y.val hyp
  · intro hx
    let y := foldedOpposition K x
    have hyp : y.val∈Positive K :=
      (opposition_mem_iff CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K true x.val).mpr hx
    refine ⟨y,(le_of_eq (positiveSylow_coe K p).symm) hyp,?_⟩
    exact foldedOpposition_involutive K x

end SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeSylow
