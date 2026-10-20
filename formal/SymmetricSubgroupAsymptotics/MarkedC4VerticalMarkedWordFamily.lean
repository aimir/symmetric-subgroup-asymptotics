import SymmetricSubgroupAsymptotics.MarkedC4GraphAnnihilatorPackets
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedHallFibre
import SymmetricSubgroupAsymptotics.MarkedC4VerticalHallBase

/-! The ACTUAL enlarged family closed under physical peels.
Vertical mark subgroups are allowed; physical projections remain full.
Original character graphs inject into this finite family, and its true
zero-physical base is derived from the one global Hall polynomial. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.VerticalMarkedWordFamily
open FiniteOrbitWordShapes FiniteBinaryWordTargets

variable {C b : ℕ} (T : Target C b)
abbrev Marks (r : ℕ) := Multiplicative (Fin r → ZMod 4)
abbrev Ambient := Product T.letters

/-- Each retained physical coordinate is full. No condition forces the
single global mark coordinate to be full, faithful, or a graph. -/
abbrev Family (r : ℕ) := {J : Subgroup (Ambient T × Marks r) //
  ∀ i,Function.Surjective (fun h : J => h.val.1 i)}
local instance familyFintype (r : ℕ) : Fintype (Family T r) := Fintype.ofFinite _

def count (r : ℕ) : ℝ := Nat.card (Family T r)

/-- An original whole character graph is an actual member of the enlarged
family, before any physical annihilator or quotient is selected. -/
def graphCode (r : ℕ) (z : GraphAnnihilatorPackets.Object T (Marks r)) : Family T r := by
  refine ⟨SubgroupCharacterGraph.graph z.val.1 z.val.2,?_⟩
  intro i g
  obtain ⟨h,hh⟩ := z.property i g
  exact ⟨⟨SubgroupCharacterGraph.hom z.val.1 z.val.2 h,⟨h,rfl⟩⟩,hh⟩

theorem graphCode_injective (r : ℕ) : Function.Injective (graphCode T r) := by
  intro z w he
  apply Subtype.ext
  apply SubgroupCharacterGraph.code_injective
  exact congrArg Subtype.val he

theorem original_graph_card_le (r : ℕ) :
    Nat.card (GraphAnnihilatorPackets.Object T (Marks r)) ≤ Nat.card (Family T r) :=
  Nat.card_le_card_of_injective (graphCode T r) (graphCode_injective T r)

/-- The physical-zero enlarged family is paid by ONE vertical Hall base,
not by the original zero-degree character moment and not once per peel. -/
theorem zero_count_le (T : Target C 0) (r : ℕ) :
    (Nat.card (Family T r) : ℝ) ≤
      VerticalHallBase.polynomial r*(2 : ℝ)^markedF 0 r := by
  letI : IsEmpty (Fin T.shape.length.val) := ⟨by
    intro i
    have hi : (T.shape.degrees i).val ≤ ∑ j,(T.shape.degrees j).val :=
      Finset.single_le_sum
        (f := fun j : Fin T.shape.length.val => (T.shape.degrees j).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [T.shape.total] at hi
    exact (Nat.not_lt_of_ge hi) (T.shape.positive i)⟩
  have hpi : Function.Injective (MonoidHom.snd (Ambient T) (Marks r)) := by
    intro x y he
    exact Prod.ext (Subsingleton.elim _ _) he
  let e : Family T r → Subgroup (Marks r) := fun J =>
    J.val.map (MonoidHom.snd (Ambient T) (Marks r))
  have he : Function.Injective e := by
    intro J K h
    apply Subtype.ext
    exact Subgroup.map_injective hpi h
  exact (Nat.cast_le.mpr (Nat.card_le_card_of_injective e he)).trans
    (VerticalHallBase.card_subgroups_le r)

end SymmetricSubgroupAsymptotics.MarkedC4.VerticalMarkedWordFamily
