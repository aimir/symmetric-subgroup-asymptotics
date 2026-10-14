import SymmetricSubgroupAsymptotics.BinaryCentralOmegaExtensionRank
import SymmetricSubgroupAsymptotics.BinaryPrimaryPrefixFixedRank
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity
import SymmetricSubgroupAsymptotics.Non2SchurBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# A designated binary prefix over a commutative binary top

An original elementary-binary module extension of a commutative binary
top is binary. If its module has Schur capacity at most `a` and the top
has central binary rank at most `b`, the whole central rank is at most
`a+b`, while the derived-central rank is at most `a`. This constructs a
binary-primary linear prefix and the required relative orbit slots when
`a+b <= r+1` and `a <= r`.

The module is the original extension kernel, with its original conjugation
chart. In characteristic two, binary groups have only fixed simple types;
the existing p-group Schur theorem supplies that fact here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

theorem isPGroup_of_kernel_and_target
    {Q B : Type} [Group Q] [Group B] (pi : Q →* B)
    (hker : IsPGroup 2 pi.ker) (hB : IsPGroup 2 B) : IsPGroup 2 Q := by
  have h := (hB.to_subgroup (⊤ : Subgroup B)).comap_of_ker_isPGroup pi hker
  have htop : IsPGroup 2 (⊤ : Subgroup Q) := by
    simpa only [Subgroup.comap_top] using h
  exact htop.of_equiv Subgroup.topEquiv

/-- Rank bounds alone construct the literal one-binary-prefix orbit
input on a finite binary group. The prefix target is its finite image. -/
theorem nonempty_binaryPrefixOrbitInput_of_ranks
    {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (r : ℕ)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ r + 1)
    (hderived : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator Q)) ≤ r) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 r)) := by
  obtain ⟨χ, hχ, hresidual⟩ :=
    exists_binaryPrimaryLinearCharacter_residual_rank_le (k := ℂ)
      r hcentral hderived
  letI : Finite χ.range :=
    Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hfixed : Module.finrank (ZMod 2)
      (binaryKernelOmegaConjugationRepresentation χ.rangeRestrict).invariants ≤ r := by
    have hresidual' : Module.finrank (ZMod 2)
        (binaryCentralOmegaSubmodule χ.rangeRestrict.ker) ≤ r := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hresidual
    exact (binaryKernelOmega_invariants_finrank_le_centralResidual
      χ.rangeRestrict).trans hresidual'
  have hcapacity : representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation χ.rangeRestrict)).toRepresentation ≤ r := by
    rw [pGroup_representationSchurCapacity hQ,
      finiteRepresentationSocle_invariants_finrank_eq]
    exact_mod_cast hfixed
  refine ⟨DegreeTwoPairRelativeKernelOrbitInput.ofSocleSchurCapacity
    (profile := degreeTwoPairRelativeProfile 1 0 0 r)
    χ.rangeRestrict (fun _ ↦ χ) (fun _ ↦ hχ)
    Fin.elim0 Fin.elim0 ?_ (hQ.to_subgroup _) hcapacity⟩
  rw [MonoidHom.ker_rangeRestrict]
  ext q
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  constructor
  · intro h
    exact ⟨⟨fun _ ↦ h, fun i ↦ Fin.elim0 i⟩, fun i ↦ Fin.elim0 i⟩
  · intro h
    exact h.1.1 (0 : Fin 1)

/-- A reusable binary branch for actual (possibly nonsplit) extensions.
The only capacity input is the actual kernel module's Schur bound. -/
theorem nonempty_binaryPrefixOrbitInput_of_abelianTop
    {Q B : Type} [Group Q] [Finite Q] [Group B] [Finite B]
    [IsMulCommutative B]
    (pi : Q →* B) (hpi : Function.Surjective pi)
    (A : Rep (ZMod 2) B) [Finite A] (E : OriginalKernelModuleChart pi A)
    (hB : IsPGroup 2 B) (a b r : ℕ)
    (hmodule : representationSchurCapacity A.ρ ≤ a)
    (htop : Module.finrank (ZMod 2) (Additive (binaryCentralOmega B)) ≤ b)
    (hsum : a + b ≤ r + 1) (hderived : a ≤ r) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 r)) := by
  have hfixed : Module.finrank (ZMod 2) A.ρ.invariants ≤ a := by
    rw [pGroup_representationSchurCapacity hB] at hmodule
    exact_mod_cast hmodule
  have hker : IsPGroup 2 pi.ker :=
    (primeModule_isPGroup 2 A).of_equiv E.equiv
  have hQ : IsPGroup 2 Q := isPGroup_of_kernel_and_target pi hker hB
  apply nonempty_binaryPrefixOrbitInput_of_ranks hQ r
  · exact (E.central_finrank_le_invariants_add_top hpi).trans
      ((Nat.add_le_add hfixed htop).trans hsum)
  · exact (E.derivedCentral_finrank_le_invariants hpi).trans
      (hfixed.trans hderived)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
