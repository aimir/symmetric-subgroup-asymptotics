import SymmetricSubgroupAsymptotics.BinaryTransgressionExact
import SymmetricSubgroupAsymptotics.PrimeFrattiniSurjection
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalHead

/-! The actual H² inflation defect in an original full subdirect product.
Its increment is bounded by the relative head of the literal first axis
inside the complete evaluation kernel. No proxy dimension replaces H². -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- Prime and binary evaluation use the same actual characters and map. -/
theorem terminalRestrictedInflationKernel_finrank_eq_primeRelativeHead
    (T : Type) [Group T] [Finite T] :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T) =
      Module.finrank (ZMod 2)
        (primeRelativeCharacters 2 (primeAbelianizationGroupMap 2 T).ker) :=
  terminalRestrictedInflationKernel_finrank_eq_relativeHead T

private theorem relativeHead_eq_of_subgroup_eq
    {G : Type} [Group G] (N L : Subgroup G) [N.Normal] [L.Normal] (h : N=L) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) := by
  subst L
  rfl

/-- The terminal inflation increment is controlled on the original
nonabelian pair core by its exact evaluation-kernel axis under all of A. -/
theorem binarySubdirect_inflation_le
    {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (K : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    let M := (primeAbelianizationGroupMap 2 K).ker
    letI := SubdirectNormalHead.firstAxis_normal K M hA
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K) ≤
      Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (SubdirectNormalHead.firstAxis K M)) := by
  let M := (primeAbelianizationGroupMap 2 K).ker
  letI := SubdirectNormalHead.firstAxis_normal K M hA
  letI := SubdirectNormalHead.secondImage_normal K M hB
  have himage : SubdirectNormalHead.secondImage K M =
      (primeAbelianizationGroupMap 2 B).ker :=
    primeAbelianizationGroupMap_ker_map 2 (subdirectSecond K) hB
  have h := SubdirectNormalHead.relativeHead_le K M 2 hA hB
  rw [relativeHead_eq_of_subgroup_eq _ _ himage] at h
  simpa only [terminalRestrictedInflationKernel_finrank_eq_primeRelativeHead] using h

end SymmetricSubgroupAsymptotics
