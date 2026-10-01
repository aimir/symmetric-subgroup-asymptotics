import SymmetricSubgroupAsymptotics.DegreeSixOwnerInducedHead
import SymmetricSubgroupAsymptotics.SurjectiveCoinducedDescent

/-!
# Degree-six owner bounds for arbitrary injected coinduced layers

The owner estimates are stated on the representation actually produced by a
local chief factor.  No subrepresentation presentation is required: an
injective intertwiner into the literal coinduced function model is enough.
This is the form preserved by quotient descent from an imprimitive action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

section FixedIntertwiner

variable {k G V U : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]

/-- An intertwiner sends the fixed space of one element into the corresponding
fixed space of its target representation. -/
def intertwinerElementFixedMap
    (τ : Representation k G U) (σ : Representation k G V)
    (φ : τ.IntertwiningMap σ) (g : G) :
    representationElementFixedSpace τ g →ₗ[k]
      representationElementFixedSpace σ g where
  toFun u := ⟨φ u.1, by
    apply (mem_representationElementFixedSpace σ g _).mpr
    have hu := (mem_representationElementFixedSpace τ g u.1).mp u.2
    have hi := Representation.IntertwiningMap.isIntertwining τ σ φ g u.1
    exact hi.symm.trans (congrArg φ hu)⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add φ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul φ _ _

theorem intertwinerElementFixedMap_injective
    (τ : Representation k G U) (σ : Representation k G V)
    (φ : τ.IntertwiningMap σ) (hφ : Function.Injective φ) (g : G) :
    Function.Injective (intertwinerElementFixedMap τ σ φ g) := by
  intro u v huv
  apply Subtype.ext
  exact hφ (congrArg Subtype.val huv)

end FixedIntertwiner


/-- A cyclic orbit on the actual coset space controls every representation
injected into the corresponding coinduced model. -/
theorem coinduced_injective_characterHead_le_fibre_of_pretransitive
    {p : ℕ} [Fact p.Prime] {G V U : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup G) (ρ : Representation (ZMod p) H V) (g : G)
    [MulAction.IsPretransitive (Subgroup.zpowers g) (G ⧸ H)]
    (τ : Representation (ZMod p) G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hφ : Function.Injective φ) :
    Module.finrank (ZMod p)
        (primeActionCharacters p (representationGroupAction τ)) ≤
      Module.finrank (ZMod p) V := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional (ZMod p) U :=
    FiniteDimensional.of_injective φ.toLinearMap hφ
  calc
    Module.finrank (ZMod p)
        (primeActionCharacters p (representationGroupAction τ)) =
        Module.finrank (ZMod p)
          (τ.IntertwiningMap (Representation.trivial (ZMod p) G (ZMod p))) :=
      (representationCharacterHeadEquiv τ).finrank_eq
    _ ≤ Module.finrank (ZMod p) (representationElementFixedSpace τ g) :=
      representationHead_le_elementFixedSpace τ g
    _ ≤ Module.finrank (ZMod p)
        (representationElementFixedSpace (Representation.coind H.subtype ρ) g) :=
      (intertwinerElementFixedMap τ _ φ g).finrank_le_finrank_of_injective
        (intertwinerElementFixedMap_injective τ _ φ hφ g)
    _ ≤ Module.finrank (ZMod p) V :=
      coinduced_elementFixedSpace_le_fibre H ρ g
        (cyclicRightCosetCover_of_pretransitive H g)

namespace C1OddIndexTwoOwnerWitness

variable {X : Type} [Finite X] {G : Subgroup (Equiv.Perm X)}
    (W : C1OddIndexTwoOwnerWitness G)

include W in
/-- The literal six-cycle controls every representation injected into the
coinduced point-stabilizer model. -/
theorem coinduced_injective_characterHead_le_fibre
    [MulAction.IsPretransitive G X]
    (hX : Nat.card X = 6)
    (M₀ : Subgroup G) [M₀.Normal]
    (hM₀ : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M₀) ≠ 0)
    (x : X)
    {V U : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    [AddCommGroup U] [Module (ZMod 3) U]
    (ρ : Representation (ZMod 3) (MulAction.stabilizer G x) V)
    (τ : Representation (ZMod 3) G U)
    (φ : τ.IntertwiningMap
      (Representation.coind (MulAction.stabilizer G x).subtype ρ))
    (hφ : Function.Injective φ) :
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction τ)) ≤
      Module.finrank (ZMod 3) V := by
  obtain ⟨g, hg⟩ := W.exists_six_cycle_of_relativeHead_ne_zero hX M₀ hM₀
  letI : MulAction.IsPretransitive (Subgroup.zpowers g) X := hg
  letI : MulAction.IsPretransitive (Subgroup.zpowers g)
      (G ⧸ MulAction.stabilizer G x) :=
    cyclicQuotientStabilizer_pretransitive g x
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional (ZMod 3) U :=
    FiniteDimensional.of_injective φ.toLinearMap hφ
  calc
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction τ)) =
        Module.finrank (ZMod 3)
          (τ.IntertwiningMap (Representation.trivial (ZMod 3) G (ZMod 3))) :=
      (representationCharacterHeadEquiv τ).finrank_eq
    _ ≤ Module.finrank (ZMod 3) (representationElementFixedSpace τ g) :=
      representationHead_le_elementFixedSpace τ g
    _ ≤ Module.finrank (ZMod 3)
        (representationElementFixedSpace
          (Representation.coind (MulAction.stabilizer G x).subtype ρ) g) :=
      (intertwinerElementFixedMap τ _ φ g).finrank_le_finrank_of_injective
        (intertwinerElementFixedMap_injective τ _ φ hφ g)
    _ ≤ Module.finrank (ZMod 3) V :=
      coinduced_elementFixedSpace_le_fibre (MulAction.stabilizer G x) ρ g
        (cyclicRightCosetCover_of_pretransitive _ g)

end C1OddIndexTwoOwnerWitness

namespace C1CyclicBinaryModuleOwnerWitness

variable {k G V U : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup U] [Module k U]
    (W : C1CyclicBinaryModuleOwnerWitness G)

/-- Evaluate the base-invariant vectors of an arbitrary injected coinduced
representation on the literal complement. -/
def coinducedInvariantEvalComplement
    [W.base.Normal]
    (H : Subgroup G) (ρ : Representation k H V)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ)) :
    Representation.IntertwiningMap
      ((Representation.toInvariants τ W.base).comp W.complement.subtype)
      (Representation.coind (⊥ : Subgroup W.complement).subtype
        (Representation.trivial k (⊥ : Subgroup W.complement) V)) where
  toFun u := ⟨fun p => (φ u.1).1 (p : G), by
    intro h p
    have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2)
    subst h
    simp⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext p
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 (p : G))
      (map_add φ _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    funext p
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 (p : G))
      (map_smul φ _ _)
  isIntertwining' p := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext q
    change (φ (τ (p : G) u.1)).1 (q : G) =
      (φ u.1).1 ((q : G) * (p : G))
    have hi := Representation.IntertwiningMap.isIntertwining τ
      (Representation.coind H.subtype ρ) φ (p : G) u.1
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 (q : G)) hi

theorem coinducedInvariantEvalComplement_injective
    [W.base.Normal]
    (H : Subgroup G) (ρ : Representation k H V)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hφ : Function.Injective φ) :
    Function.Injective (coinducedInvariantEvalComplement W H ρ τ φ) := by
  intro u v huv
  apply Subtype.ext
  apply hφ
  apply Subtype.ext
  funext x
  let b : W.base := W.factorBase x
  let p : W.complement := W.factorComplement x
  let b' : W.base := normalConjugate W.base W.base_normal b ((p : G)⁻¹)
  have hxbp : (b : G) * (p : G) = x := W.factorization x
  have hpb : (p : G) * (b' : G) = x := by
    calc
      (p : G) * (b' : G) = (b : G) * (p : G) := by
        simp only [b', normalConjugate_coe]
        group
      _ = x := hxbp
  have hufix : φ u.1 = Representation.coind H.subtype ρ (b' : G) (φ u.1) := by
    have huB := u.2 b'
    have he := congrArg φ huB
    have hi := Representation.IntertwiningMap.isIntertwining τ
      (Representation.coind H.subtype ρ) φ (b' : G) u.1
    exact he.symm.trans hi
  have hvfix : φ v.1 = Representation.coind H.subtype ρ (b' : G) (φ v.1) := by
    have hvB := v.2 b'
    have he := congrArg φ hvB
    have hi := Representation.IntertwiningMap.isIntertwining τ
      (Representation.coind H.subtype ρ) φ (b' : G) v.1
    exact he.symm.trans hi
  rw [← hpb]
  have huval := congrArg
    (fun f : Representation.coindV H.subtype ρ => f.1 (p : G)) hufix
  have hvval := congrArg
    (fun f : Representation.coindV H.subtype ρ => f.1 (p : G)) hvfix
  change (φ u.1).1 (p : G) = (φ u.1).1 ((p : G) * (b' : G)) at huval
  change (φ v.1).1 (p : G) = (φ v.1).1 ((p : G) * (b' : G)) at hvval
  change (φ u.1).1 ((p : G) * (b' : G)) =
    (φ v.1).1 ((p : G) * (b' : G))
  rw [← huval, ← hvval]
  exact congrFun (congrArg Subtype.val huv) p

/-- The cyclic-binary owner bound for every representation injected into the
literal coinduced model. -/
theorem coinduced_injective_characterHead_le_fibre
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    [Module (ZMod 3) U]
    (hPcard : Nat.card W.complement = 3)
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (τ : Representation (ZMod 3) G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hφ : Function.Injective φ) :
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction τ)) ≤
      Module.finrank (ZMod 3) V := by
  letI : W.base.Normal := W.base_normal
  letI : Fintype W.base := Fintype.ofFinite W.base
  obtain ⟨n, hn⟩ := W.basePGroup.exists_card_eq
  have hcard3 : (Fintype.card W.base : ZMod 3) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, hn, Nat.cast_pow]
    exact pow_ne_zero n (by decide)
  letI : Invertible (Fintype.card W.base : ZMod 3) := invertibleOfNonzero hcard3
  letI : FiniteDimensional (ZMod 3) U :=
    FiniteDimensional.of_injective φ.toLinearMap hφ
  let τB := Representation.toInvariants τ W.base
  let τP := τB.comp W.complement.subtype
  let ρ₀ : Representation (ZMod 3) (⊥ : Subgroup W.complement) V :=
    Representation.trivial (ZMod 3) (⊥ : Subgroup W.complement) V
  have hindex : (⊥ : Subgroup W.complement).index = 3 ^ 1 := by
    rw [Subgroup.index_bot, hPcard]
    norm_num
  calc
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction τ)) =
        Module.finrank (ZMod 3)
          (τ.IntertwiningMap (Representation.trivial (ZMod 3) G (ZMod 3))) :=
      (representationCharacterHeadEquiv τ).finrank_eq
    _ ≤ Module.finrank (ZMod 3)
          (τB.IntertwiningMap (Representation.trivial (ZMod 3) G (ZMod 3))) :=
      representationHead_le_normalInvariants τ W.base
    _ = Module.finrank (ZMod 3)
          (primeActionCharacters 3 (representationGroupAction τB)) :=
      (representationCharacterHeadEquiv τB).finrank_eq.symm
    _ ≤ Module.finrank (ZMod 3)
          (primeActionCharacters 3 (representationGroupAction τP)) :=
      representationCharacterHead_le_restriction τB W.complement.subtype
    _ ≤ Module.finrank (ZMod 3) V * ternaryLocalWidth 1 :=
      threeGroup_coinduced_injective_characterHead_le W.complementPGroup
        (⊥ : Subgroup W.complement) ρ₀ 1 hindex τP
        (coinducedInvariantEvalComplement W H ρ τ φ)
        (coinducedInvariantEvalComplement_injective W H ρ τ φ hφ)
    _ = Module.finrank (ZMod 3) V := by simp

end C1CyclicBinaryModuleOwnerWitness

end SymmetricSubgroupAsymptotics

end
