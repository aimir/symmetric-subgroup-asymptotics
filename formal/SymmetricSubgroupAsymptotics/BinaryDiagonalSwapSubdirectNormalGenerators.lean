import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapSubdirect
import SymmetricSubgroupAsymptotics.NormalGeneratorExtension
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles

/-! The subdirect dichotomy gives uniform ambient normal generators, hence
socle generators for every original normal quotient. In the graph branch
one binary quotient position is added to the local affine bound; in the
full-fiber branch the supplied bound belongs to the entire model. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwapSubdirect

open SemidirectProduct BinaryDiagonalSwap

variable {V R : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V) (G : Subgroup (Model φ))

theorem normal_generating_tuples (hirr : Irreducible φ)
    (hsurj : Function.Surjective (first φ G))
    (hdiag : ∀ v : V, (inl (v, v) : Model φ) ∈ G)
    (hswap : (inr (1, C2Wreath.gen) : Model φ) ∈ G)
    {a : ℕ}
    (hlocal : ∀ N : Subgroup (Local φ), N.Normal →
      ∃ x : Fin a → Local φ, Subgroup.normalClosure (Set.range x) = N)
    (hfull : ∀ N : Subgroup (Model φ), N.Normal →
      ∃ x : Fin (a + 1) → Model φ, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (a + 1) → G, Subgroup.normalClosure (Set.range x) = N := by
  rcases first_injective_or_eq_top φ G hirr hsurj hdiag hswap with hinj | htop
  · let e : Even φ G ≃* Local φ := MulEquiv.ofBijective (first φ G) ⟨hinj, hsurj⟩
    exact normal_generating_tuples_of_kernel_and_image (parity φ G)
      (parity_surjective φ G hswap)
      (normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective hlocal)
      normal_generating_singletons_of_isCyclic
  · let e : G ≃* Model φ := (MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv)
    exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective hfull

theorem quotientSocle (hirr : Irreducible φ)
    (hsurj : Function.Surjective (first φ G))
    (hdiag : ∀ v : V, (inl (v, v) : Model φ) ∈ G)
    (hswap : (inr (1, C2Wreath.gen) : Model φ) ∈ G)
    {a : ℕ}
    (hlocal : ∀ N : Subgroup (Local φ), N.Normal →
      ∃ x : Fin a → Local φ, Subgroup.normalClosure (Set.range x) = N)
    (hfull : ∀ N : Subgroup (Model φ), N.Normal →
      ∃ x : Fin (a + 1) → Model φ, Subgroup.normalClosure (Set.range x) = N)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) (a + 1) :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples φ G hirr hsurj hdiag hswap hlocal hfull) N

end BinaryDiagonalSwapSubdirect
end SymmetricSubgroupAsymptotics

end
