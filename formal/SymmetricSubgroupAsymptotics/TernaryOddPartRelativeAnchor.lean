import SymmetricSubgroupAsymptotics.TernaryOddPartCharacterAnchor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelAnchor
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One ordinary anchor for groups with odd part three

A jointly faithful irreducible tuple with a binary-kernel member gives one
ordinary prefix and a relative tail consisting of the other original
irreducibles. Normal restriction constituents are constructed by Maschke.
The prefix kernel and every representation are retained literally.

For a group of order `2^a * 3`, the kernel-anchor theorem finds the required
member of any faithful tuple. Thus a socle-generator bound of `r + 1`,
together with the published Zmud input, yields the relative profile
`(0, 0, 1, r)`. Establishing that socle bound for an actual quotient remains
a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairRelativeKernelAnchor

/-- Reindex an existing faithful tuple around its designated binary-kernel
member. Each relative slot is the same whole-group irreducible as before;
only an actual constituent of its normal restriction is chosen. -/
noncomputable def ofFaithfulTupleBinaryKernel
    {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    (rho : Fin (r + 1) → FiniteIrreducibleRepresentation ℂ Q)
    (hfaithful : ∀ q : Q, (∀ i, (rho i).action q = 1) → q = 1)
    (anchor : Fin (r + 1)) (hbinary : IsPGroup 2 (rho anchor).action.ker) :
    DegreeTwoPairRelativeKernelAnchor Q
      (degreeTwoPairOrdinaryRelativeProfile 1 r) where
  binary := Fin.elim0
  binary_twoGroup := fun i ↦ Fin.elim0 i
  linear := Fin.elim0
  ordinary := fun _ ↦ rho anchor
  relative := fun i ↦ rho (anchor.succAbove i)
  kernel := (rho anchor).action.ker
  kernel_eq := by
    ext q
    simp only [degreeTwoPairOrdinaryRelativeProfile, Subgroup.mem_inf,
      Subgroup.mem_iInf, MonoidHom.mem_ker]
    simp
  kernel_twoGroup := hbinary
  constituent := fun i ↦ NormalRestrictionConstituent.choose
    (rho (anchor.succAbove i)).action (rho anchor).action.ker
  faithful := by
    intro q _ _ hp ht
    apply hfaithful q
    exact (Fin.forall_iff_succAbove anchor).mpr ⟨hp (0 : Fin 1), ht⟩

/-- The odd-part condition finds an anchor inside the original tuple. -/
noncomputable def ofTernaryOddPartFaithfulTuple
    {Q : Type} [Group Q] [Finite Q] {a r : ℕ}
    (hcard : Nat.card Q = 2 ^ a * 3)
    (rho : Fin (r + 1) → FiniteIrreducibleRepresentation ℂ Q)
    (hfaithful : ∀ q : Q, (∀ i, (rho i).action q = 1) → q = 1) :
    DegreeTwoPairRelativeKernelAnchor Q
      (degreeTwoPairOrdinaryRelativeProfile 1 r) := by
  let h := faithfulIrreducibleTuple_exists_binary_kernel_of_ternaryOddPart
    hcard rho hfaithful
  exact ofFaithfulTupleBinaryKernel rho hfaithful h.choose h.choose_spec

/-- An `r + 1`-generator socle bound supplies one ordinary character and
`r` relative characters whenever the group's odd part is exactly three. -/
noncomputable def ofTernaryOddPartSocleGeneratorBound
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {Q : Type} [Group Q] [Finite Q] {a r : ℕ}
    (hcard : Nat.card Q = 2 ^ a * 3)
    (hgen : SocleNormalGeneratorBound Q (r + 1)) :
    DegreeTwoPairRelativeKernelAnchor Q
      (degreeTwoPairOrdinaryRelativeProfile 1 r) := by
  let data := hZmud Q (r + 1) hgen
  exact ofTernaryOddPartFaithfulTuple hcard data.choose data.choose_spec

end DegreeTwoPairRelativeKernelAnchor
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
