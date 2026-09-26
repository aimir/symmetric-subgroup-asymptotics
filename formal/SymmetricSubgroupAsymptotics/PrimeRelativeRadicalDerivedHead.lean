import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank
import SymmetricSubgroupAsymptotics.PrimeRelativeRadical
import SymmetricSubgroupAsymptotics.PrimeFrattini

/-! One ambient kernel containment controls the second-radical head of
EVERY original normal subgroup. In finite p-groups the premise is the
actual Frattini containment. It must be checked on the ambient group; it
is not valid for arbitrary binary groups such as a cyclic group of order4. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]

/-- The same actual relative radical belongs to the original axis cap. -/
theorem primeRelativeRadical_le_axis_derived_of_evaluation_kernel_le
    (hG : (primeAbelianizationGroupMap p G).ker ≤ commutator G) :
    primeRelativeRadical p N ≤ N ⊓ commutator G :=
  le_inf (primeRelativeRadical_le p N)
    ((primeRelativeRadical_le_ambient_evaluation_ker p N).trans hG)

/-- The second-radical head is bounded by the existing maximum over all
original ambient normals; no separate radical-rank certificate is needed. -/
theorem primeRelativeRadical_head_le_axis_max_of_evaluation_kernel_le
    (hG : (primeAbelianizationGroupMap p G).ker ≤ commutator G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p (primeRelativeRadical p N)) ≤
      primeNormalHeadMax p (N ⊓ commutator G) :=
  primeRelativeHead_le_normalHeadMax p _ _
    (primeRelativeRadical_le_axis_derived_of_evaluation_kernel_le p N hG)

/-- A single actual Frattini containment applies to every original normal
of the same finite p-group, while keeping whole-G conjugation throughout. -/
theorem primeRelativeRadical_head_le_axis_max_of_frattini_le
    (hG : IsPGroup p G) (hPhi : frattini G ≤ commutator G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p (primeRelativeRadical p N)) ≤
      primeNormalHeadMax p (N ⊓ commutator G) := by
  apply primeRelativeRadical_head_le_axis_max_of_evaluation_kernel_le p N
  rwa [primeAbelianizationGroupMap_ker p G hG]

end SymmetricSubgroupAsymptotics
