import SymmetricSubgroupAsymptotics.BinaryTransgressionExact
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelQuotients

/-! The actual H² inflation defect is bounded by the original derived-normal
rank when the canonical evaluation kernel lies in the derived subgroup.
The exact transgression theorem identifies this same kernel's relative head;
no proxy for cohomology, intrinsic kernel action, or splitting is substituted. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The actual evaluation kernel is an eligible original ambient normal
in the definition of rho. Exact transgression therefore gives tau ≤ rho. -/
theorem terminalRestrictedInflationKernel_finrank_le_derivedNormalRank
    (T : Type) [Group T] [Finite T]
    (hT : (primeAbelianizationGroupMap 2 T).ker ≤ commutator T) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T) ≤
      primeDerivedNormalRank 2 T := by
  rw [terminalRestrictedInflationKernel_finrank_eq_relativeHead]
  change Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 (primeAbelianizationGroupMap 2 T).ker) ≤
    primeNormalHeadMax 2 (commutator T)
  exact primeRelativeHead_le_normalHeadMax 2 (commutator T)
    (primeAbelianizationGroupMap 2 T).ker hT

/-- A fixed master supplies this bound for every actual epimorphic image;
the target is retained in both the cohomology and derived-normal ranks. -/
theorem terminalRestrictedInflationKernel_finrank_le_derivedNormalRank_of_surjective
    {G H : Type} [Group G] [Group H] [Finite H]
    (β : G →* H) (hβ : Function.Surjective β)
    (hG : (primeAbelianizationGroupMap 2 G).ker ≤ commutator G) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) ≤
      primeDerivedNormalRank 2 H :=
  terminalRestrictedInflationKernel_finrank_le_derivedNormalRank H
    (primeEvaluationKernel_le_commutator_of_surjective 2 β hβ hG)

/-- The same conclusion for each literal original normal quotient. -/
theorem terminalRestrictedInflationKernel_quotient_finrank_le_derivedNormalRank
    {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hG : (primeAbelianizationGroupMap 2 G).ker ≤ commutator G) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel (G ⧸ N)) ≤
      primeDerivedNormalRank 2 (G ⧸ N) :=
  terminalRestrictedInflationKernel_finrank_le_derivedNormalRank (G ⧸ N)
    (primeEvaluationKernel_quotient_le_commutator 2 N hG)

end SymmetricSubgroupAsymptotics
