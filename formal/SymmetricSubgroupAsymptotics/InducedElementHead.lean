import SymmetricSubgroupAsymptotics.RepresentationElementHead
import Mathlib.RepresentationTheory.FiniteIndex

/-! A single actual cyclic coset orbit bounds every induced subrepresentation
head by the original fibre dimension. The coinduced function relation retains
all original fibre twists; neither semisimplicity nor a Gaussian estimate is
assumed. The transitivity hypothesis concerns the actual action on `G ⧸ H`. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

private theorem representation_fixed_zpow (τ : Representation k G V)
    (g : G) (v : V) (hv : τ g v = v) (n : ℤ) : τ (g ^ n) v = v := by
  let S : Subgroup G := {
    carrier := {x | τ x v = v}
    one_mem' := by change τ 1 v = v; rw [map_one]; rfl
    mul_mem' := by
      intro x y hx hy
      change τ (x*y) v = v
      rw [map_mul]
      change τ x (τ y v) = v
      rw [hy, hx]
    inv_mem' := by
      intro x hx
      change τ x⁻¹ v = v
      have he := congrArg (τ x⁻¹) hx
      change (τ x⁻¹ * τ x) v = τ x⁻¹ v at he
      rw [← map_mul, inv_mul_cancel, map_one] at he
      exact he.symm }
  exact S.zpow_mem hv n

/-- Literal right-coset normal forms sufficient for the function-model argument. -/
def cyclicRightCosetCover (H : Subgroup G) (g : G) : Prop :=
  ∀ x : G, ∃ h : H, ∃ n : ℤ, (h : G) * g ^ n = x

/-- Transitivity of the actual cyclic subgroup on the actual left cosets gives
right-coset normal forms by inversion; no coset representative table is assumed. -/
theorem cyclicRightCosetCover_of_pretransitive (H : Subgroup G) (g : G)
    [MulAction.IsPretransitive (Subgroup.zpowers g) (G ⧸ H)] :
    cyclicRightCosetCover H g := by
  intro x
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (Subgroup.zpowers g)
    ((1 : G) : G ⧸ H) ((x⁻¹ : G) : G ⧸ H)
  change (((a : G) * 1 : G) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) at ha
  simp only [mul_one] at ha
  have hm : x * (a : G) ∈ H := by
    have hi := H.inv_mem (QuotientGroup.eq.mp ha)
    simpa only [mul_inv_rev, inv_inv] using hi
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
  refine ⟨⟨x * (a : G), hm⟩, -n, ?_⟩
  change (x * (a : G)) * g ^ (-n) = x
  rw [zpow_neg, hn, mul_assoc, mul_inv_cancel, mul_one]

/-- Evaluation at the identity, restricted to the actual element-fixed space. -/
def coinducedElementFixedEval (H : Subgroup G) (ρ : Representation k H V) (g : G) :
    representationElementFixedSpace (Representation.coind H.subtype ρ) g →ₗ[k] V where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Fixedness under the actual right translation by `g` propagates to its
integer powers, while left translation still uses the original `ρ(h)` twist. -/
theorem coinducedElementFixedEval_injective (H : Subgroup G)
    (ρ : Representation k H V) (g : G) (hcover : cyclicRightCosetCover H g) :
    Function.Injective (coinducedElementFixedEval H ρ g) := by
  have hp : ∀ (f : representationElementFixedSpace (Representation.coind H.subtype ρ) g)
      (n : ℤ), f.1.1 (g ^ n) = f.1.1 1 := by
    intro f n
    have hf := representation_fixed_zpow (Representation.coind H.subtype ρ) g f.1
      ((mem_representationElementFixedSpace _ _ _).mp f.2) n
    have he := congrArg (fun u : Representation.coindV H.subtype ρ => u.1 1) hf
    change f.1.1 (1 * g ^ n) = f.1.1 1 at he
    simpa only [one_mul] using he
  intro f f' he
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨h, n, rfl⟩ := hcover x
  change f.1.1 (H.subtype h * g ^ n) = f'.1.1 (H.subtype h * g ^ n)
  rw [f.1.2 h (g ^ n), f'.1.2 h (g ^ n), hp f n, hp f' n]
  exact congrArg (ρ h) he

theorem coinduced_elementFixedSpace_le_fibre [FiniteDimensional k V]
    (H : Subgroup G) (ρ : Representation k H V) (g : G)
    (hcover : cyclicRightCosetCover H g) :
    Module.finrank k (representationElementFixedSpace (Representation.coind H.subtype ρ) g) ≤
      Module.finrank k V :=
  (coinducedElementFixedEval H ρ g).finrank_le_finrank_of_injective
    (coinducedElementFixedEval_injective H ρ g hcover)

/-- The standard finite-index equivalence retains the actual induction data. -/
def inducedElementCoinducedEquiv (H : Subgroup G) [H.FiniteIndex]
    (ρ : Representation k H V) :
    (Representation.ind H.subtype ρ).Equiv (Representation.coind H.subtype ρ) := by
  classical
  exact Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))

def inducedElementFixedToCoinduced (H : Subgroup G) [H.FiniteIndex]
    (ρ : Representation k H V) (g : G) :
    representationElementFixedSpace (Representation.ind H.subtype ρ) g →ₗ[k]
      representationElementFixedSpace (Representation.coind H.subtype ρ) g where
  toFun v := ⟨inducedElementCoinducedEquiv H ρ v.1, by
    apply (mem_representationElementFixedSpace _ _ _).mpr
    have hv := (mem_representationElementFixedSpace _ _ _).mp v.2
    exact (Representation.IntertwiningMap.isIntertwining _ _
      (inducedElementCoinducedEquiv H ρ).toIntertwiningMap g v.1).symm.trans
        (congrArg (inducedElementCoinducedEquiv H ρ) hv)⟩
  map_add' v w := by apply Subtype.ext; exact map_add (inducedElementCoinducedEquiv H ρ) _ _
  map_smul' a v := by apply Subtype.ext; exact map_smul (inducedElementCoinducedEquiv H ρ) _ _

theorem induced_elementFixedSpace_le_fibre [FiniteDimensional k V]
    (H : Subgroup G) [H.FiniteIndex] (ρ : Representation k H V) (g : G)
    (hcover : cyclicRightCosetCover H g) :
    Module.finrank k (representationElementFixedSpace (Representation.ind H.subtype ρ) g) ≤
      Module.finrank k V := by
  let ev := (coinducedElementFixedEval H ρ g).comp (inducedElementFixedToCoinduced H ρ g)
  apply ev.finrank_le_finrank_of_injective
  intro v w h
  have he := coinducedElementFixedEval_injective H ρ g hcover h
  apply Subtype.ext
  exact (inducedElementCoinducedEquiv H ρ).toLinearEquiv.injective (congrArg Subtype.val he)

/-- Every subrepresentation of the original induced representation satisfies
the fibre bound if one specified actual element is transitive on its cosets. -/
theorem induced_subrepresentationCharacterHead_le_fibre_of_pretransitive
    {p : ℕ} [Fact p.Prime] {G₀ V₀ : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀]
    (H : Subgroup G₀) (ρ : Representation (ZMod p) H V₀) (g : G₀)
    [MulAction.IsPretransitive (Subgroup.zpowers g) (G₀ ⧸ H)]
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Module.finrank (ZMod p) V₀ := by
  letI : Fintype G₀ := Fintype.ofFinite G₀
  letI : FiniteDimensional (ZMod p) (Representation.IndV H.subtype ρ) :=
    FiniteDimensional.of_injective (inducedElementCoinducedEquiv H ρ).toLinearEquiv.toLinearMap
      (inducedElementCoinducedEquiv H ρ).toLinearEquiv.injective
  exact (subrepresentationCharacterHead_le_ambient_elementFixedSpace
    (Representation.ind H.subtype ρ) M g).trans
      (induced_elementFixedSpace_le_fibre H ρ g
        (cyclicRightCosetCover_of_pretransitive H g))

end SymmetricSubgroupAsymptotics
