import SymmetricSubgroupAsymptotics.BinaryPairUniformQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.CoprimeCyclicElementarySocles
import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators

/-! The cyclic coarse-top branch on six original points has a normally
cyclic socle in EVERY original quotient. The correlated binary kernel is
retained, and coprime prime-type sharing avoids adding a top generator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPointThreePairCubicQuotientSocles

variable {T : Subgroup (Equiv.Perm (Fin 6))} (E : BinaryPairFrame T (Fin 3))

include E in
 theorem quotient [MulAction.IsPretransitive T (Fin 6)]
    (hTop : Nat.card E.top.range=3) (N : Subgroup T) [N.Normal] :
    SocleNormalGeneratorBound (T ⧸ N) 1 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive E.top.range (Fin 3) := E.top_pretransitive
  letI : NeZero (Nat.card E.top.range : ZMod 2) := ⟨by rw [hTop]; decide +kernel⟩
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 3)) 1 := by
    apply permutationFunctionRepresentation_uniform_of_invertible_orbitCover
      (fun _ : Fin 1 => (0 : Fin 3))
    intro x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq E.top.range (0 : Fin 3) x
    exact ⟨0,g,hg⟩
  let C := E.elementaryKernelChart
  have hcard : Nat.card (T ⧸ E.top.ker)=3 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange E.top).toEquiv).trans hTop
  letI : IsCyclic (T ⧸ E.top.ker) := isCyclic_of_prime_card hcard
  have hcop : Nat.Coprime C.p (Nat.card (T ⧸ E.top.ker)) := by
    change Nat.Coprime 2 (Nat.card (T ⧸ E.top.ker))
    rw [hcard]
    decide +kernel
  have hkernel : UniformSubrepresentationGeneratorBound C.quotientRepresentation.ρ 1 :=
    E.elementaryKernelChart_uniform 1 hu
  let identity : C.quotientRepresentation.ρ.IntertwiningMap C.quotientRepresentation.ρ :=
    { toLinearMap := LinearMap.id,isIntertwining' _ := rfl }
  have hgen : RepresentationGeneratedBy C.quotientRepresentation.ρ 1 :=
    representationGeneratedBy_of_injective_of_uniform hkernel identity (fun _ _ h => h)
  exact CoprimeCyclicElementarySocles.quotient E.top.ker C hcop hgen N

end SymmetricSubgroupAsymptotics.SixPointThreePairCubicQuotientSocles
