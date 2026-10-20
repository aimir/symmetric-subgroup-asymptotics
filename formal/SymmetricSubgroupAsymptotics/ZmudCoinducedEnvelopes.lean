import SymmetricSubgroupAsymptotics.ZmudFixedSpaceConstituents
import SymmetricSubgroupAsymptotics.CentralCharacterConstituent
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Coinduction from a literal subgroup preserves absence of fixed vectors
for every ambient-normal subgroup contained in that subgroup. Scalar
characters of elementary abelian groups use the injective standard
additive character of the prime field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ZmudCoinducedEnvelopes

/-- Ambient normality is exactly what transports fixed vectors across
all the right cosets in an actual coinduction. -/
theorem coinduced_fixedFree
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (sigma : Representation k H V)
    (hfix : ∀ v : V, (∀ n : N, sigma ⟨n.1, hNH n.2⟩ v = v) → v = 0)
    (f : Representation.coindV H.subtype sigma)
    (hf : ∀ n : N, Representation.coind H.subtype sigma n.1 f = f) :
    f = 0 := by
  apply Subtype.ext
  funext g
  apply hfix
  intro n
  let m : N := ⟨g⁻¹ * n.1 * g, by
    simpa only [inv_inv] using
      Subgroup.Normal.conj_mem inferInstance n.1 n.2 g⁻¹⟩
  have he := congrArg (fun u : Representation.coindV H.subtype sigma => u.1 g) (hf m)
  change f.1 (g * (g⁻¹ * n.1 * g)) = f.1 g at he
  have hmul : g * (g⁻¹ * n.1 * g) = n.1 * g := by group
  rw [hmul] at he
  change f.1 (H.subtype (⟨n.1, hNH n.2⟩ : H) * g) = f.1 g at he
  rw [f.2 (⟨n.1, hNH n.2⟩ : H) g] at he
  exact he

/-- The exact finite nonzero scalar coinduction, bundled for constituent
selection. -/
def scalarEnvelope {G : Type} [Group G] [Finite G]
    (H : Subgroup G) (chi : H →* ℂ) :
    ZmudFixedSpaceConstituents.Envelope G := by
  let W := Representation.coindV H.subtype (scalarCharacterRepresentation chi)
  letI : Fintype G := Fintype.ofFinite G
  letI : Nontrivial W := by
    refine ⟨⟨scalarCharacterSupported H chi, 0, ?_⟩⟩
    intro he
    have hz := congrArg (fun v : W => v.1 1) he
    change (scalarCharacterSupported H chi).1 1 = 0 at hz
    rw [scalarCharacterSupported_one] at hz
    exact one_ne_zero hz
  exact {
    Space := W
    addCommGroup := inferInstance
    module := inferInstance
    finiteDimensional := inferInstance
    nontrivial := inferInstance
    action := Representation.coind H.subtype (scalarCharacterRepresentation chi) }

/-- A scalar character nontrivial on an ambient-normal subgroup makes the
entire coinduced envelope fixed-free for that subgroup. -/
theorem scalarEnvelope_fixedFree
    {G : Type} [Group G] [Finite G]
    (H N : Subgroup G) [N.Normal] (hNH : N ≤ H) (chi : H →* ℂ)
    (hchi : ∃ n : N, chi ⟨n.1, hNH n.2⟩ ≠ 1)
    (f : (scalarEnvelope H chi).Space)
    (hf : ∀ n : N, (scalarEnvelope H chi).action n.1 f = f) :
    f = 0 := by
  apply coinduced_fixedFree H N hNH (scalarCharacterRepresentation chi) ?_ f hf
  intro z hz
  obtain ⟨n, hn⟩ := hchi
  have he := hz n
  change chi ⟨n.1, hNH n.2⟩ * z = z at he
  have hmul : (chi ⟨n.1, hNH n.2⟩ - 1) * z = 0 := by
    rw [sub_mul, one_mul, he, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hn)

/-- The actual complex character attached to a prime-field linear form. -/
def elementaryCharacter
    {p : ℕ} [NeZero p] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (l : Module.Dual (ZMod p) V) : Multiplicative V →* ℂ :=
  (ZMod.stdAddChar (N := p)).toMonoidHom.comp l.toAddMonoidHom.toMultiplicative

/-- Conversion to complex roots of unity loses no prime-field value. -/
theorem elementaryCharacter_eq_one_iff
    {p : ℕ} [NeZero p] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (l : Module.Dual (ZMod p) V) (v : Multiplicative V) :
    elementaryCharacter l v = 1 ↔ l v.toAdd = 0 := by
  change ZMod.stdAddChar (l v.toAdd) = 1 ↔ l v.toAdd = 0
  rw [← (ZMod.stdAddChar (N := p)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff]

end SymmetricSubgroupAsymptotics.ZmudCoinducedEnvelopes
