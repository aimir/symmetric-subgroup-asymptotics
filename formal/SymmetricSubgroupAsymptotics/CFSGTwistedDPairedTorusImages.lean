import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusWords
import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootImages
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkNodeTori

/-! The natural image of the original paired fixed torus word. Both
terminal factors and their field parameters are retained literally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusImages
open CFSG.Models.Chevalley CFSGSerreOrdinaryTwists
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDForkNodeTori CFSGTwistedDFixedA2
open CFSGTwistedDPairedTorusWords CFSGTwistedDPairedRootImages
open CFSGTwistedDFixedCentralCocycle

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def frobeniusUnit (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) : (q.Extension 2)ˣ :=
  Units.map (definingFieldAutomorphism q 2).toMonoidHom c

theorem frobeniusUnit_val (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    (frobeniusUnit q c : q.Extension 2) = (c : q.Extension 2) ^ q.order :=
  definingFieldAutomorphism_apply q 2 c

theorem wordParameter_frobenius (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    (fun i => (wordParameter c i) ^ q.order) = wordParameter (frobeniusUnit q c) := by
  funext i
  have hσ (a : q.Extension 2) := definingFieldAutomorphism_apply q 2 a
  change (wordParameter c i) ^ q.order = _
  rw [← hσ]
  fin_cases i <;>
    simp [wordParameter, frobeniusUnit, map_sub, map_inv₀, map_neg]

def pairedNaturalTorus (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    elementaryRootGroup (q.Extension 2) (s + 4) :=
  nodeTorus (q.Extension 2) (s + 2) (pen (s + 2)) c *
    nodeTorus (q.Extension 2) (s + 2) (last (s + 2)) (frobeniusUnit q c)

theorem nodeWord_image (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 4))
    (c : (q.Extension 2)ˣ) :
    orthogonalImageRepresentation (q.Extension 2) (s + 4) (rank_ge_four s)
        (nodeWord s q i (wordParameter c)) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
        (nodeTorus (q.Extension 2) (s + 2) i c) := by
  simp only [nodeWord, nodeTorus, map_mul, root_image]
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  change ν (naturalRoot s q false i ((c : q.Extension 2) - 1)) *
      ν (naturalRoot s q true i 1) *
      ν (naturalRoot s q false i ((c : q.Extension 2)⁻¹ - 1)) *
      ν (naturalRoot s q true i (-(c : q.Extension 2))) =
    ν (naturalRoot s q false i ((c : q.Extension 2) - 1) *
      naturalRoot s q true i 1 *
      naturalRoot s q false i ((c : q.Extension 2)⁻¹ - 1) *
      naturalRoot s q true i (-(c : q.Extension 2)))
  rw [ν.map_mul, ν.map_mul, ν.map_mul]

theorem pairedTorus_image (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    fixedImageAction s q (pairedTorus s q c) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
        (pairedNaturalTorus s q c) := by
  let ρ := orthogonalImageRepresentation (q.Extension 2) (s + 4) (rank_ge_four s)
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  change ρ (toModel s q (pairedTorus s q c)) = ν (pairedNaturalTorus s q c)
  rw [pairedTorus_toModel, wordParameter_frobenius]
  calc
    _ = ρ (nodeWord s q (pen (s + 2)) (wordParameter c)) *
        ρ (nodeWord s q (last (s + 2)) (wordParameter (frobeniusUnit q c))) :=
      ρ.map_mul _ _
    _ = ν (nodeTorus (q.Extension 2) (s + 2) (pen (s + 2)) c) *
        ν (nodeTorus (q.Extension 2) (s + 2) (last (s + 2)) (frobeniusUnit q c)) :=
      congrArg₂ (fun a b => a * b) (nodeWord_image s q (pen (s + 2)) c)
        (nodeWord_image s q (last (s + 2)) (frobeniusUnit q c))
    _ = _ := (ν.map_mul _ _).symm

def pairedDiagonal (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    Index (s + 4) → q.Extension 2 :=
  fun i => chainDiagonal (q.Extension 2) (s + 2) c i *
    forkDiagonal (q.Extension 2) (s + 2) (frobeniusUnit q c) i

theorem pairedNaturalTorus_val (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    ((pairedNaturalTorus s q c).val : Mat (q.Extension 2) (s + 4)) =
      Matrix.diagonal (pairedDiagonal s q c) := by
  change ((nodeTorus (q.Extension 2) (s + 2) (pen (s + 2)) c).val :
      Mat (q.Extension 2) (s + 4)) *
    ((nodeTorus (q.Extension 2) (s + 2) (last (s + 2)) (frobeniusUnit q c)).val :
      Mat (q.Extension 2) (s + 4)) = _
  rw [nodeTorus_pen_val, nodeTorus_last_val, Matrix.diagonal_mul_diagonal]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusImages
