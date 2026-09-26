import SymmetricSubgroupAsymptotics.SubgroupTailFibre
import SymmetricSubgroupAsymptotics.BinaryCarrierWord
import SymmetricSubgroupAsymptotics.TerminalImageCounts

/-! Exact terminal fibres of a literal critical-plus-carrier product.
Only the individual original nonabelian critical coordinates are full;
the projection to their whole product need not be full. Extra regular
coordinate conditions and survival remain predicates on the original K.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

variable {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)

def terminalCoordinatesFull {B : Type} [Group B]
    (K : Subgroup (CriticalProductGroup a s × B)) : Prop :=
  ∀ i, K.map ((criticalProductFactorProjection a s i).comp
    (MonoidHom.fst (CriticalProductGroup a s) B)) = ⊤

/-- Including the actual tail subgroup does not change any first-side
critical coordinate. The entire first-side image can remain proper. -/
theorem terminalCoordinatesFull_map_inclusion {B : Type} [Group B]
    (L : Subgroup B) (J : Subgroup (CriticalProductGroup a s × L)) :
    terminalCoordinatesFull a s (J.map (SubdirectTailImage.inclusion L)) ↔
      terminalCoordinatesFull a s J := by
  have he (i : ι) :
      (J.map (SubdirectTailImage.inclusion L)).map
          ((criticalProductFactorProjection a s i).comp
            (MonoidHom.fst (CriticalProductGroup a s) B)) =
        J.map ((criticalProductFactorProjection a s i).comp
          (MonoidHom.fst (CriticalProductGroup a s) L)) := by
    rw [Subgroup.map_map]
    rfl
  unfold terminalCoordinatesFull
  simp only [he]

/-- The actual subgroups of the fixed product, with full carrier
coordinates and full individual critical factors. P is tested on K itself. -/
abbrev TerminalProductFamily (w : List Factor)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop) :=
  {K : Subgroup (CriticalProductGroup a s × Product w) //
    Full w (SubdirectTailImage.tail K) ∧ terminalCoordinatesFull a s K ∧ P K}

/-- Exact decomposition by the unique literal H = K.map snd. A terminal
fibre is attached once to this complete H, with P pulled back by inclusion. -/
def terminalProductFamilyEquiv (w : List Factor)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop) :
    TerminalProductFamily a s w P ≃
      Σ H : Family w,
        {J : TerminalActualSubgroups a s H.1 //
          P (J.1.map (SubdirectTailImage.inclusion H.1))} :=
  (SubgroupTailFibre.equiv (Full w) (fun K => terminalCoordinatesFull a s K ∧ P K)).trans
    (Equiv.sigmaCongrRight fun H =>
      { toFun := fun J =>
          ⟨⟨J.1,J.2.1,
            (terminalCoordinatesFull_map_inclusion a s H.1 J.1).mp J.2.2.1⟩,J.2.2.2⟩
        invFun := fun J =>
          ⟨J.1.1,J.1.2.1,
            (terminalCoordinatesFull_map_inclusion a s H.1 J.1.1).mpr J.1.2.2,J.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })

@[simp] theorem terminalProductFamilyEquiv_tail (w : List Factor)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop)
    (K : TerminalProductFamily a s w P) :
    (terminalProductFamilyEquiv a s w P K).1.1 = SubdirectTailImage.tail K.1 := rfl

/-- Decoding retains the complete original subgroup, not just its image
or an abstract isomorphism type. -/
theorem terminalProductFamilyEquiv_decode (w : List Factor)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop)
    (K : TerminalProductFamily a s w P) :
    (terminalProductFamilyEquiv a s w P K).2.1.1.map
        (SubdirectTailImage.inclusion (terminalProductFamilyEquiv a s w P K).1.1) = K.1 :=
  SubdirectTailImage.core_map K.1

local instance terminalSubgroupFinite {G : Type} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- The fixed-product family and its full terminal-fibre sum have exactly
the same multiplicity, including the empty carrier word. -/
theorem terminalProductFamily_card (w : List Factor)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop) :
    Nat.card (TerminalProductFamily a s w P) =
      ∑ H : Family w,
        Nat.card {J : TerminalActualSubgroups a s H.1 //
          P (J.1.map (SubdirectTailImage.inclusion H.1))} := by
  rw [Nat.card_congr (terminalProductFamilyEquiv a s w P), Nat.card_sigma]

theorem terminalProductFamily_card_real (w : List Factor)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop) :
    (Nat.card (TerminalProductFamily a s w P) : ℝ) =
      ∑ H : Family w,
        (Nat.card {J : TerminalActualSubgroups a s H.1 //
          P (J.1.map (SubdirectTailImage.inclusion H.1))} : ℝ) := by
  exact_mod_cast terminalProductFamily_card a s w P

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
