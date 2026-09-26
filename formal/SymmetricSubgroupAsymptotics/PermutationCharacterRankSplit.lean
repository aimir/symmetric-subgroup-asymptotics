import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Finite.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Equiv.Sum

/-! The intransitive character-rank step for an actual permutation action.
Restriction to an invariant subset gives its literal permutation image.
The actual kernel acts faithfully on the complementary original points.
The extension inequality and relative-to-absolute inclusion then split
the rank. No comparison of a subgroup's rank with its ambient rank is used.
The final induction interface still requires the bounds on smaller actions. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

variable {G X : Type*} [Group G] [MulAction G X]

/-- Restrict the original action to precisely the original invariant set. -/
def restrictionHom (S : SubMulAction G X) : G →* Equiv.Perm S :=
  MulAction.toPermHom G S

/-- The actual restriction image, with its natural faithful action on S. -/
abbrev Image (S : SubMulAction G X) : Subgroup (Equiv.Perm S) :=
  (restrictionHom S).range

def projection (S : SubMulAction G X) : G →* Image S :=
  (restrictionHom S).rangeRestrict

theorem projection_surjective (S : SubMulAction G X) :
    Function.Surjective (projection S) :=
  (restrictionHom S).rangeRestrict_surjective

/-- Use the kernel of the very map appearing in the extension theorem. -/
abbrev Kernel (S : SubMulAction G X) : Subgroup G := (projection S).ker

@[simp] theorem projection_original (S : SubMulAction G X) (g : G) (x : S) :
    (((projection S g : Equiv.Perm S) x) : X) = g • (x : X) := rfl

theorem image_faithful (S : SubMulAction G X) : FaithfulSMul (Image S) S :=
  inferInstance

instance imageFinite [Finite G] (S : SubMulAction G X) : Finite (Image S) :=
  Finite.of_surjective (projection S) (projection_surjective S)

theorem image_isPGroup (S : SubMulAction G X) (p : ℕ) (hG : IsPGroup p G) :
    IsPGroup p (Image S) :=
  hG.of_surjective (projection S) (projection_surjective S)

theorem kernel_isPGroup (S : SubMulAction G X) (p : ℕ) (hG : IsPGroup p G) :
    IsPGroup p (Kernel S) := hG.to_subgroup (Kernel S)

/-- Every element of this literal kernel fixes every original point of S. -/
theorem kernel_fixes (S : SubMulAction G X) (g : Kernel S) (x : S) :
    (g : G) • (x : X) = (x : X) := by
  have hπ : projection S (g : G) = 1 := g.property
  have hρ : restrictionHom S (g : G) = 1 :=
    congrArg (fun a : Image S => (a : Equiv.Perm S)) hπ
  exact congrArg Subtype.val (Equiv.congr_fun hρ x)

/-- The complementary action is restriction through the same inclusion
of the actual kernel into G, not an independently chosen permutation model. -/
@[simp] theorem kernel_complement_original (S : SubMulAction G X)
    (g : Kernel S) (x : ↥(Sᶜ)) :
    ((g • x : ↥(Sᶜ)) : X) = (g : G) • (x : X) := rfl

theorem kernel_complement_faithful [FaithfulSMul G X] (S : SubMulAction G X) :
    FaithfulSMul (Kernel S) ↥(Sᶜ) := by
  classical
  refine ⟨?_⟩
  intro a b h
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := X)
  intro x
  by_cases hx : x ∈ S
  · exact (kernel_fixes S a ⟨x, hx⟩).trans (kernel_fixes S b ⟨x, hx⟩).symm
  · exact congrArg (fun z : ↥(Sᶜ) => (z : X)) (h ⟨x, hx⟩)

/-- Relative kernel characters are a subspace of the absolute characters
of that very kernel. No surjectivity of character restriction is assumed. -/
theorem rank_le_image_add_kernel [Finite G] (S : SubMulAction G X)
    (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤
      Module.finrank (ZMod p) (PrimeCharacters p (Image S)) +
        Module.finrank (ZMod p) (PrimeCharacters p (Kernel S)) := by
  have h := primeCharacterRank_extension_le p (projection S) (projection_surjective S)
  exact h.trans (Nat.add_le_add_left
    (Submodule.finrank_le (primeRelativeCharacters p (Kernel S))) _)

/-- The two point sets partition the original point set literally. -/
theorem card_split [Finite X] (S : SubMulAction G X) :
    Nat.card S + Nat.card ↥(Sᶜ) = Nat.card X := by
  classical
  simpa only [Nat.card_sum] using
    Nat.card_congr (Equiv.sumCompl (fun x : X => x ∈ S))

theorem degrees_lt [Finite X] (S : SubMulAction G X)
    (hS : (S : Set X).Nonempty) (hC : (Sᶜ : Set X).Nonempty) :
    Nat.card S < Nat.card X ∧ Nat.card ↥(Sᶜ) < Nat.card X := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y, hy⟩ := hC
  exact ⟨Finite.card_subtype_lt (p := fun z : X => z ∈ S) hy,
    Finite.card_subtype_lt (p := fun z : X => z ∈ Sᶜ) (x := x) (fun h => h hx)⟩

/-- The exact floor arithmetic needs neither even orbit sizes nor an
assumption on the parity of either complementary degree. -/
theorem rank_le_card_div [Finite G] [Finite X] (S : SubMulAction G X)
    (p : ℕ) [Fact p.Prime]
    (hI : Module.finrank (ZMod p) (PrimeCharacters p (Image S)) ≤ Nat.card S / p)
    (hK : Module.finrank (ZMod p) (PrimeCharacters p (Kernel S)) ≤ Nat.card ↥(Sᶜ) / p) :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ Nat.card X / p := by
  refine (rank_le_image_add_kernel S p).trans ((Nat.add_le_add hI hK).trans ?_)
  simpa only [card_split S] using Nat.add_div_le_add_div (Nat.card S) (Nat.card ↥(Sᶜ)) p

/-- An actual orbit, without any change of original point labels. -/
def orbitSubset (x : X) : SubMulAction G X where
  carrier := MulAction.orbit G x
  smul_mem' g _ hx := MulAction.mem_orbit_of_mem_orbit g hx

theorem exists_nonempty_proper_invariant (h : ¬ MulAction.IsPretransitive G X) :
    ∃ S : SubMulAction G X, (S : Set X).Nonempty ∧ (Sᶜ : Set X).Nonempty := by
  classical
  have hxy : ∃ x y : X, ¬ ∃ g : G, g • x = y := by
    by_contra hn
    apply h
    refine ⟨?_⟩
    intro x y
    by_contra hno
    exact hn ⟨x, y, hno⟩
  obtain ⟨x, y, hxy⟩ := hxy
  refine ⟨orbitSubset x, ⟨x, MulAction.mem_orbit_self x⟩, y, ?_⟩
  intro hy
  exact hxy (MulAction.mem_orbit_iff.mp hy)

end SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

namespace SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

/-- A strong-induction step using only the same bound on strictly smaller
actual faithful 2-group actions. Both original restriction maps are fixed. -/
theorem binary_rank_le_half_of_smaller_actions (S : SubMulAction G X)
    (hG : IsPGroup 2 G) (hS : (S : Set X).Nonempty) (hC : (Sᶜ : Set X).Nonempty)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Module.finrank (ZMod 2) (PrimeCharacters 2 H) ≤ Nat.card Y / 2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) ≤ Nat.card X / 2 := by
  letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
  have hlt := degrees_lt S hS hC
  exact rank_le_card_div S 2
    (hsmaller (Image S) S (image_isPGroup S 2 hG) hlt.1)
    (hsmaller (Kernel S) ↥(Sᶜ) (kernel_isPGroup S 2 hG) hlt.2)

/-- The complete intransitive branch. The transitive bound remains the
other induction branch and is not assumed or proved by this module. -/
theorem binary_rank_le_half_of_intransitive
    (hG : IsPGroup 2 G) (hnot : ¬ MulAction.IsPretransitive G X)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Module.finrank (ZMod 2) (PrimeCharacters 2 H) ≤ Nat.card Y / 2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) ≤ Nat.card X / 2 := by
  obtain ⟨S, hS, hC⟩ := exists_nonempty_proper_invariant hnot
  exact binary_rank_le_half_of_smaller_actions S hG hS hC hsmaller

end SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit
