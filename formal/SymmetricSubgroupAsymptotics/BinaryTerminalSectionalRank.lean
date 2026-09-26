import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.BinaryTransgressionExact

/-! The terminal H² inflation defect is controlled by the sectional bound
of the original ambient group. The subgroup to which that bound is applied
is the actual evaluation kernel inside the actual terminal subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A faithful original embedding bounds the actual terminal inflation
kernel, using exact transgression and the full character space of its kernel. -/
theorem terminalRestrictedInflationKernel_finrank_le_of_sectionalBound
    {G T : Type} [Group G] [Finite G] [Group T] [Finite T]
    (r : ℕ) (hG : PrimeSectionalRankBound 2 G r)
    (f : T →* G) (hf : Function.Injective f) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T) ≤ r := by
  rw [terminalRestrictedInflationKernel_finrank_eq_relativeHead]
  let K := (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)).ker
  exact (Submodule.finrank_le (primeRelativeCharacters 2 K)).trans
    (primeCharacterRank_le_of_injective 2 hG (f.comp K.subtype)
      (hf.comp Subtype.val_injective))

/-- Every original subgroup of C4^a × B satisfies the terminal defect
bound a+u. There is no fullness condition on either original projection. -/
theorem terminalRestrictedInflationKernel_cyclicFour_subgroup_le
    (a : ℕ) (B : Type) [Group B] [Finite B] (u : ℕ)
    (hB : Nat.card B ≤ 2 ^ u)
    (H : Subgroup (Multiplicative (Fin a → ZMod 4) × B)) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) ≤ a + u :=
  terminalRestrictedInflationKernel_finrank_le_of_sectionalBound (a + u)
    (binarySectionalRankBound_cyclicFour_prod a B u hB)
    H.subtype Subtype.val_injective

end SymmetricSubgroupAsymptotics
