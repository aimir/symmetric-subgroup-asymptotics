import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup

/-! The concrete first-pair stabilizer is exactly the smaller elementary
symplectic group, not only a subgroup injecting into its matrix units. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K]

def firstPairTailToElementary (r : ℕ) :
    firstPairElementary K r →* elementaryRootGroup K r where
  toFun u := ⟨firstPairTailHom K r u,
    all_formPreserving_elementary K r _
      (tailUnits_preserves_pairing r u.val u.property.2
        (preservesPairing_of_form (r + 1) _
          (elementaryRootGroup_le_formPreserving K (r + 1) u.property.1)))⟩
  map_one' := Subtype.ext (map_one (firstPairTailHom K r))
  map_mul' u v := Subtype.ext (map_mul (firstPairTailHom K r) u v)

theorem firstPairTailToElementary_bijective (r : ℕ) :
    Function.Bijective (firstPairTailToElementary K r) := by
  constructor
  · intro u v h
    exact firstPairTailHom_injective K r (congrArg Subtype.val h)
  · intro v
    obtain ⟨u, hu⟩ := elementaryRootGroup_le_firstPairTail_range K r v.property
    exact ⟨u, Subtype.ext hu⟩

def firstPairTailEquiv (r : ℕ) : firstPairElementary K r ≃* elementaryRootGroup K r :=
  MulEquiv.ofBijective (firstPairTailToElementary K r) (firstPairTailToElementary_bijective K r)

theorem firstPairElementary_card (r : ℕ) :
    Nat.card (firstPairElementary K r) = Nat.card (elementaryRootGroup K r) :=
  Nat.card_congr (firstPairTailEquiv K r).toEquiv

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
