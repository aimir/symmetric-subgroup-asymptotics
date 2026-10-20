import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernaryOrbitGenerators
import SymmetricSubgroupAsymptotics.SplitAffineLiteralSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Exact signed ternary affine lifts yield original quotient and joint
packages. Coordinate signs may vary between blocks. Pure complement
membership must be proved by actual lifted words (possibly after a point
gauge); it is never inferred from the block permutation image alone. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernarySplitJointData
open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelveJointFiniteRows

variable {H : Type} [Group H] [Finite H]
  (b : H →* Equiv.Perm (Fin 4)) (d : H → Fin 4 → ZMod 3)
  (hone : ∀ i, d 1 i=1)
  (hmul : ∀ g h i, d (g*h) i=d g i*d h (b g⁻¹ i))

abbrev Model := TernaryMonomialCocycle.Model b d hone hmul

def literalAction (points : Fin 4 × ZMod 3 ≃ Fin 12) :
    Model b d hone hmul →* Equiv.Perm (Fin 12) :=
  points.permCongrHom.toMonoidHom.comp (TernaryMonomialCocycle.action b d hone hmul)

variable {n : ℕ} (points : Fin 4 × ZMod 3 ≃ Fin 12)
  (lifted : Fin n → Model b d hone hmul) (target : Fin n → Equiv.Perm (Fin 12))
  (hbinding : ∀ i, literalAction b d hone hmul points (lifted i)=target i)
  (hcomplement : ∀ h : H, (inr h : Model b d hone hmul) ∈
    Subgroup.closure (Set.range lifted))
  (hcop : Nat.Coprime 3 (Nat.card H))
  (origin : Fin 4) (horbit : ∀ i : Fin 4, ∃ h : H, b h origin=i)
  (normalTuples : ∀ L : Subgroup H, L.Normal →
    ∃ x : Fin 2 → H, Subgroup.normalClosure (Set.range x)=L)

include hbinding hcomplement hcop horbit normalTuples in
theorem original_quotientSocle_at_two
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range target)) ⧸ N) 2 := by
  have hgen : RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation
        (TernaryMonomialCocycle.linearAction b d hone hmul)) 1 := by
    apply TwelvePointRemainingStructuralTernaryOrbitGenerators.generatedBy_orbitCover
      b d hone hmul (fun _ : Fin 1 => origin)
    intro i
    obtain ⟨h,hh⟩ := horbit i
    exact ⟨0,h,hh⟩
  have hnormal (L : Subgroup H) (hL : L.Normal) : MarkedC4.normalGen L ≤ 2 := by
    obtain ⟨x,hx⟩ := normalTuples L hL
    exact normalGen_le_of_fin_tuple x hx
  exact SplitAffineLiteralSocles.quotientSocle
    (TernaryMonomialCocycle.linearAction b d hone hmul)
    (literalAction b d hone hmul points) lifted target (Equiv.refl _)
    hbinding hcomplement hcop 1 2 hgen hnormal N

include hbinding hcomplement hcop horbit normalTuples in
def jointDataAtTwo (I : DegreeTwoPairTopFiniteInterface 12)
    (hTop : I.top=Subgroup.closure (Set.range target))
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) I.top (Fin 12)) 2) :
    DegreeTwoTwelveFlexibleProfiles.Data I := by
  have hs : ∀ U : Subgroup (Equiv.Perm (Fin 12)),
      U=Subgroup.closure (Set.range target) →
      ∀ R : FiniteNormalStateRegistry U, R.QuotientSocleGeneratorFamily 2 := by
    intro U hU
    subst U
    intro R
    exact .ofQuotientBounds R (fun N => by
      letI := N.2
      exact original_quotientSocle_at_two b d hone hmul points lifted target
        hbinding hcomplement hcop origin horbit normalTuples N.1)
  let finite : DegreeTwoTwelveJointFiniteRowData I 2 2 :=
    { topSocle := hs I.top hTop I.normalRegistry, natural := natural }
  exact .ofExact finite (by decide +kernel)

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernarySplitJointData
