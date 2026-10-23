import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedPathAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleStabilizer
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyIndex

/-! The literal original signed-chart stabilizer has index at most two
in the opposed-Sylow stabilizer. The label can be identity or path
reversal; no preservation of root length is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleStabilizerIndex
open CFSGFFourE6OriginalSignedPathAction CFSGFFourE6OriginalSimpleStabilizer
open CFSGFFourE6OriginalSimpleParameters CFSGFourRootPathPermutation
open CFSGSubgroupFamilyIndex CFSG.Models.Chevalley

private def signedPathPermutation (sigma : pathAut) : Equiv.Perm (Bool×Fin 4) :=
  Equiv.prodCongr (Equiv.refl Bool) sigma.val

theorem simple_stabilizer_index_le_two (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (simpleStabilizer K p).index≤2 := by
  classical
  let Allowed := {tau : Equiv.Perm (Bool×Fin 4) //
    ∃sigma : pathAut,signedPathPermutation sigma=tau}
  have hindex : (simpleStabilizer K p).index≤Nat.card Allowed := by
    apply family_index_le_permutations (pairStabilizer K p)
      (fun z : Bool×Fin 4=>(originalSimpleHom K z.1 z.2).range)
      (fun tau=>∃sigma : pathAut,signedPathPermutation sigma=tau)
    intro f
    obtain ⟨sigma,hsigma⟩ := exists_original_signed_path_permutation K p f.val
      (pair_preserves_positive K p f) (pair_preserves_negative K p f)
    exact ⟨signedPathPermutation sigma,⟨sigma,rfl⟩,fun z=>hsigma z.1 z.2⟩
  have hcard : Nat.card Allowed≤Nat.card pathAut := by
    let label : pathAut→Allowed := fun sigma=>⟨signedPathPermutation sigma,⟨sigma,rfl⟩⟩
    have hsurj : Function.Surjective label := by
      rintro ⟨tau,sigma,he⟩
      exact ⟨sigma,Subtype.ext he⟩
    exact Nat.card_le_card_of_surjective label hsurj
  exact (hindex.trans hcard).trans pathAut_card_le_two

end SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleStabilizerIndex
