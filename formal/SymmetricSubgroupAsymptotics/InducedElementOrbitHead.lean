import SymmetricSubgroupAsymptotics.InducedElementHead
import Mathlib.GroupTheory.DoubleCoset

/-! Actual finite cyclic-orbit representatives bound the invariant character
head of every original induced subrepresentation. The coverage hypothesis
is an equality in the original group and the coinduced fibre twists remain
unchanged. No orbit classification or literature estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A finite family meeting every literal `H`-left, `⟨g⟩`-right double coset. -/
def cyclicOrbitRepresentativeCover {ι : Type} (H : Subgroup G) (g : G)
    (rep : ι → G) : Prop :=
  ∀ x : G, ∃ i : ι, ∃ h : H, ∃ n : ℤ, (h : G) * rep i * g ^ n = x

/-- Fixed coinduced vectors are constant under actual right translation
by every integer power of the chosen element, at every group argument. -/
theorem coinducedElementFixed_apply_mul_zpow (H : Subgroup G)
    (ρ : Representation k H V) (g : G)
    (f : representationElementFixedSpace (Representation.coind H.subtype ρ) g)
    (x : G) (n : ℤ) : f.1.1 (x * g ^ n) = f.1.1 x := by
  let S : Subgroup G := {
    carrier := {a | ∀ y : G, f.1.1 (y*a) = f.1.1 y}
    one_mem' := by intro y; rw [mul_one]
    mul_mem' := by
      intro a b ha hb y
      rw [← mul_assoc, hb, ha]
    inv_mem' := by
      intro a ha y
      have he := ha (y*a⁻¹)
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he.symm }
  have hg : g ∈ S := by
    intro y
    have hf := (mem_representationElementFixedSpace _ _ _).mp f.2
    exact congrArg (fun u : Representation.coindV H.subtype ρ => u.1 y) hf
  exact S.zpow_mem hg n x

/-- Evaluate a fixed vector at the specified actual orbit representatives. -/
def coinducedElementFixedOrbitEval {ι : Type} (H : Subgroup G)
    (ρ : Representation k H V) (g : G) (rep : ι → G) :
    representationElementFixedSpace (Representation.coind H.subtype ρ) g →ₗ[k] (ι → V) where
  toFun f i := f.1.1 (rep i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coinducedElementFixedOrbitEval_injective {ι : Type} (H : Subgroup G)
    (ρ : Representation k H V) (g : G) (rep : ι → G)
    (hcover : cyclicOrbitRepresentativeCover H g rep) :
    Function.Injective (coinducedElementFixedOrbitEval H ρ g rep) := by
  intro f f' he
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨i, h, n, rfl⟩ := hcover x
  change f.1.1 (H.subtype h * rep i * g ^ n) =
    f'.1.1 (H.subtype h * rep i * g ^ n)
  simp only [mul_assoc]
  rw [f.1.2 h (rep i * g ^ n), f'.1.2 h (rep i * g ^ n),
    coinducedElementFixed_apply_mul_zpow H ρ g f (rep i) n,
    coinducedElementFixed_apply_mul_zpow H ρ g f' (rep i) n]
  exact congrArg (ρ h) (congrFun he i)

theorem induced_elementFixedSpace_le_orbitRepresentatives
    {ι : Type} [Fintype ι] [FiniteDimensional k V]
    (H : Subgroup G) [H.FiniteIndex] (ρ : Representation k H V) (g : G)
    (rep : ι → G) (hcover : cyclicOrbitRepresentativeCover H g rep) :
    Module.finrank k (representationElementFixedSpace (Representation.ind H.subtype ρ) g) ≤
      Fintype.card ι * Module.finrank k V := by
  let ev := (coinducedElementFixedOrbitEval H ρ g rep).comp
    (inducedElementFixedToCoinduced H ρ g)
  have hi : Function.Injective ev := by
    intro v w h
    have he := coinducedElementFixedOrbitEval_injective H ρ g rep hcover h
    apply Subtype.ext
    exact (inducedElementCoinducedEquiv H ρ).toLinearEquiv.injective (congrArg Subtype.val he)
  have hd := ev.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul] using hd

/-- Every actual induced subrepresentation satisfies the finite-representative
bound, without a semisimplicity or splitting hypothesis. -/
theorem induced_subrepresentationCharacterHead_le_orbitRepresentatives
    {p : ℕ} [Fact p.Prime] {G₀ V₀ ι : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀] [Fintype ι]
    (H : Subgroup G₀) (ρ : Representation (ZMod p) H V₀) (g : G₀)
    (rep : ι → G₀) (hcover : cyclicOrbitRepresentativeCover H g rep)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Fintype.card ι * Module.finrank (ZMod p) V₀ := by
  letI : Fintype G₀ := Fintype.ofFinite G₀
  letI : FiniteDimensional (ZMod p) (Representation.IndV H.subtype ρ) :=
    FiniteDimensional.of_injective (inducedElementCoinducedEquiv H ρ).toLinearEquiv.toLinearMap
      (inducedElementCoinducedEquiv H ρ).toLinearEquiv.injective
  exact (subrepresentationCharacterHead_le_ambient_elementFixedSpace
    (Representation.ind H.subtype ρ) M g).trans
      (induced_elementFixedSpace_le_orbitRepresentatives H ρ g rep hcover)

/-- Canonical representatives of the literal double cosets always cover. -/
theorem cyclicOrbitRepresentativeCover_doubleCoset (H : Subgroup G) (g : G) :
    cyclicOrbitRepresentativeCover H g
      (fun q : DoubleCoset.Quotient (H : Set G) (Subgroup.zpowers g : Set G) => q.out) := by
  intro x
  let q := DoubleCoset.mk H (Subgroup.zpowers g) x
  obtain ⟨h, hh, a, ha, hx⟩ :=
    (DoubleCoset.eq H (Subgroup.zpowers g) q.out x).mp (DoubleCoset.out_eq' _ _ q)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
  refine ⟨q, ⟨h, hh⟩, n, ?_⟩
  change h * q.out * g ^ n = x
  rw [hn]
  exact hx.symm

/-- The literal double-coset count supplies the representative bound with
no extra coverage premise. It counts the actual cyclic coset orbits. -/
theorem induced_subrepresentationCharacterHead_le_cyclicDoubleCosets
    {p : ℕ} [Fact p.Prime] {G₀ V₀ : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀]
    (H : Subgroup G₀) (ρ : Representation (ZMod p) H V₀) (g : G₀)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Nat.card (DoubleCoset.Quotient (H : Set G₀) (Subgroup.zpowers g : Set G₀)) *
          Module.finrank (ZMod p) V₀ := by
  let Q := DoubleCoset.Quotient (H : Set G₀) (Subgroup.zpowers g : Set G₀)
  letI : Finite Q := Finite.of_surjective (DoubleCoset.mk H (Subgroup.zpowers g))
    (fun q => ⟨q.out, DoubleCoset.out_eq' _ _ q⟩)
  letI : Fintype Q := Fintype.ofFinite Q
  simpa only [Nat.card_eq_fintype_card] using
    induced_subrepresentationCharacterHead_le_orbitRepresentatives H ρ g
      (fun q : Q => q.out) (cyclicOrbitRepresentativeCover_doubleCoset H g) M

end SymmetricSubgroupAsymptotics
