import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Insert

/-! Actual density-admissible factor peeling.
At each stage the selected factor maximizes the density of its actual
coordinate image. The finite selection and the original factor labels are
constructed; an ordering or a density comparison is not supplied as input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauPeeling

variable {I : Type} [DecidableEq I]

/-- The head is peeled LAST in the resulting physical order. Its entire
remaining column is bounded by its own literal diagonal density. -/
inductive Plan (density : I → Finset I → ℝ) : Finset I → List I → Prop
  | nil : Plan density ∅ []
  | cons {S : Finset I} {i : I} {l : List I}
      (mem : i∈S) (maximum : ∀ j∈S,density j S≤density i S)
      (tail : Plan density (S.erase i) l) : Plan density S (i::l)

/-- Repeated finite maximization constructs the complete selection. -/
theorem exists_plan (density : I → Finset I → ℝ) (S : Finset I) :
    ∃ l,Plan density S l := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image S (fun j => density j S) hS
      obtain ⟨l,hl⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
      exact ⟨i::l,Plan.cons hi hmax hl⟩
    · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨[],Plan.nil⟩

theorem Plan.labels {density : I → Finset I → ℝ} {S : Finset I} {l : List I}
    (h : Plan density S l) : l.toFinset=S := by
  induction h with
  | nil => rfl
  | @cons S i l hi hmax htail ih =>
    simpa only [List.toFinset_cons,ih] using Finset.insert_erase hi

theorem Plan.length {density : I → Finset I → ℝ} {S : Finset I} {l : List I}
    (h : Plan density S l) : l.length=S.card := by
  induction h with
  | nil => rfl
  | @cons S i l hi hmax htail ih =>
    rw [List.length_cons,ih,Finset.card_erase_of_mem hi]
    have hp : 0<S.card := Finset.card_pos.mpr ⟨i,hi⟩
    omega

/-- Every later residual entry is bounded by the chosen head density.
This includes the next chosen diagonal, yielding the needed monotone
sequence after reversing the peeling order. -/
theorem residual_density_le {density : I → Finset I → ℝ}
    (hmono : ∀ i,Monotone (density i)) {S U : Finset I} {i : I}
    (hmax : ∀ j∈S,density j S≤density i S) (hUS : U⊆S)
    {j : I} (hj : j∈U) : density j U≤density i S :=
  (hmono j hUS).trans (hmax j (hUS hj))

section Actual
variable [Fintype I] (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i)) (weight : I → ℕ)

def coordinate (i : I) : H →* F i := (Pi.evalMonoidHom F i).comp H.subtype

def zeroOutside (S : Finset I) : Subgroup H :=
  ⨅ i : {j : I // j∉S},(coordinate F H i.val).ker

def entry (S : Finset I) (i : I) : Subgroup (F i) :=
  (zeroOutside F H S).map (coordinate F H i)

theorem entry_mono (i : I) {S U : Finset I} (hSU : S⊆U) :
    entry F H S i≤entry F H U i := by
  apply Subgroup.map_mono
  intro h hh
  simp only [zeroOutside,Subgroup.mem_iInf,MonoidHom.mem_ker,Subtype.forall] at hh ⊢
  intro j hj
  exact hh j (fun hjS => hj (hSU hjS))

/-- For binary groups this is the exact log-order density; the ceiling
form also defines and proves the construction for arbitrary finite groups. -/
def density (i : I) (S : Finset I) : ℝ :=
  (Nat.clog 2 (Nat.card (entry F H S i)) : ℝ)/(weight i : ℝ)

theorem density_mono (i : I) : Monotone (density F H weight i) := by
  intro S U hSU
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr (Nat.clog_mono_right 2
    (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective (entry_mono F H i hSU))))

/-- An actual complete original-label selection, constructed for this H. -/
theorem exists_actual_plan (S : Finset I) :
    ∃ l,Plan (density F H weight) S l ∧ l.toFinset=S ∧ l.length=S.card := by
  obtain ⟨l,hl⟩ := exists_plan (density F H weight) S
  exact ⟨l,hl,hl.labels,hl.length⟩

/-- The comparison required for each physical Case-I tableau column is
now a consequence of actual finite maximization and subgroup inclusion. -/
theorem actual_residual_density_le {S U : Finset I} {i j : I}
    (hmax : ∀ k∈S,density F H weight k S≤density F H weight i S)
    (hUS : U⊆S) (hj : j∈U) :
    density F H weight j U≤density F H weight i S :=
  residual_density_le (density_mono F H weight) hmax hUS hj
end Actual
end SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauPeeling
