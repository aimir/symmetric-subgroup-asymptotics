import SymmetricSubgroupAsymptotics.BinarySubdirectInflation
import SymmetricSubgroupAsymptotics.PrimeSubdirectRadicalCapacity

/-! The three numerical transitions for the same original full subdirect
core. The H² invariant is the actual terminal inflation kernel; the radical
is the annihilator of all whole-factor invariant characters of its axis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (K : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype))

include hB

/-- The sharp H² transition retains the relative radical term. No odd-order
argument, splitting assumption, or direct-product replacement is used. -/
theorem binarySubdirect_inflation_le_relativeRadical :
    letI := Subgroup.normal_goursatFst hA
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K) ≤
      Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B) +
      (Module.finrank (ZMod 2) (primeRelativeCharacters 2 K.goursatFst) -
        (Module.finrank (ZMod 2) (PrimeCharacters 2 K) -
          Module.finrank (ZMod 2) (PrimeCharacters 2 B))) +
      Module.finrank (ZMod 2) (primeRelativeCharacters 2
        (primeRelativeRadical 2 K.goursatFst)) := by
  letI := Subgroup.normal_goursatFst hA
  letI := subdirectEvaluationAxis_normal 2 K hA
  have hτ := binarySubdirect_inflation_le K hA hB
  have hR := subdirectEvaluationAxis_relativeHead_le 2 K hA
  have hδ := primeCharacterRank_subdirect_eq 2 K hA hB
  change Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K) ≤
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B) +
      Module.finrank (ZMod 2) (primeRelativeCharacters 2
        (subdirectEvaluationAxis 2 K)) at hτ
  omega

/-- All constraints use the same axis, retained character space and
actual H² kernel. This holds for all finite factors, including nonabelian
proper subdirect cores; no p-group hypothesis is necessary. -/
theorem binarySubdirect_joint_transition :
    letI := Subgroup.normal_goursatFst hA
    let δ := Module.finrank (ZMod 2) (PrimeCharacters 2 K) -
      Module.finrank (ZMod 2) (PrimeCharacters 2 B)
    let ε := primeDerivedNormalRank 2 K - primeDerivedNormalRank 2 B
    let k := Module.finrank (ZMod 2) (primeRelativeCharacters 2 K.goursatFst)
    let a₂ := Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 K.goursatFst))
    Module.finrank (ZMod 2) (PrimeCharacters 2 B) ≤
      Module.finrank (ZMod 2) (PrimeCharacters 2 K) ∧
    δ ≤ k ∧ ε ≤ primeSubdirectAxisNormalRank 2 K ∧
    δ + ε ≤ Nat.log 2 (Nat.card K.goursatFst) ∧
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K) ≤
      Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B) + k - δ + a₂ := by
  letI := Subgroup.normal_goursatFst hA
  obtain ⟨hmono,hδ,hε,hjoint⟩ := primeSubdirect_joint_constraints 2 K hA hB
  have hτ := binarySubdirect_inflation_le_relativeRadical K hA hB
  refine ⟨hmono,hδ,hε,hjoint,?_⟩
  dsimp only
  omega

end SymmetricSubgroupAsymptotics
