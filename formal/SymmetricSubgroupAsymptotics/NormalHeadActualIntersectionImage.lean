import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality

/-! The quotient term of the original intersection-head filtration is
exactly the relative head of the same actual image. Saturating separate
intersection and image bounds therefore retains the exact restriction
surjectivity condition needed by the mixed-radical argument. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G Q : Type} [Group G] [Group Q]
  (p : ℕ) [Fact p.Prime] (f : G →* Q) (hf : Function.Surjective f)
  (N : Subgroup G) [N.Normal]

include hf

/-- Both original quotient ambients retain precisely the original
conjugation action, through the onto actual map. -/
theorem primeRelativeHead_actual_intersection_image_eq :
    letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
    Module.finrank (ZMod p)
        (primeRelativeCharacters p (normalChainQuotient (N ⊓ f.ker) N)) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (N.map f)) := by
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : (normalChainQuotient f.ker N).map e.toMonoidHom = N.map f := by
    change (N.map (QuotientGroup.mk' f.ker)).map e.toMonoidHom = N.map f
    rw [Subgroup.map_map]
    rfl
  exact (primeRelativeHead_second_isomorphism p N f.ker).trans
    (relativeCharacterAmbientCongr p e (normalChainQuotient f.ker N) (N.map f) he).finrank_eq.symm

/-- Saturating actual intersection/image generator bounds forces exact
head additivity and both individual equalities. No splitting is asserted. -/
theorem pGroup_actual_intersection_head_additivity_of_saturation
    [Finite G] [Finite Q] (hG : IsPGroup p G)
    (a b : ℕ) (hlower : a + b ≤ MarkedC4.normalGen N)
    (hB : MarkedC4.normalGen (N ⊓ f.ker) ≤ a)
    (hD : MarkedC4.normalGen (N.map f) ≤ b) :
    (Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (N ⊓ f.ker)) +
        Module.finrank (ZMod p)
          (primeRelativeCharacters p (normalChainQuotient (N ⊓ f.ker) N))) ∧
      MarkedC4.normalGen (N ⊓ f.ker) = a ∧ MarkedC4.normalGen (N.map f) = b := by
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hQ : IsPGroup p Q := hG.of_surjective f hf
  have hh := primeRelativeHead_chain_le (N ⊓ f.ker) N p inf_le_left
  have he := primeRelativeHead_actual_intersection_image_eq p f hf N
  rw [pGroup_normalGen_eq_primeRelativeHead p hG N] at hlower
  rw [pGroup_normalGen_eq_primeRelativeHead p hG (N ⊓ f.ker)] at hB
  rw [pGroup_normalGen_eq_primeRelativeHead p hQ (N.map f)] at hD
  constructor
  · omega
  · rw [pGroup_normalGen_eq_primeRelativeHead p hG (N ⊓ f.ker),
      pGroup_normalGen_eq_primeRelativeHead p hQ (N.map f)]
    omega

end SymmetricSubgroupAsymptotics
