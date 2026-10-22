import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Basic

/-! Once the SAME global objects of every type pass through an edge,
local type permutations agree along that edge and hence throughout a
connected graph. This generic step is independent of any building or
classification claim; the actual incidence witnesses must be supplied. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4TypeCoherence
variable {V C T : Type*} (R : V → V → Prop) (I : V → C → Prop)
  (color : C → T) (f : C → C) (sigma : V → Equiv.Perm T)
  (hlocal : ∀ v c, I v c → color (f c) = sigma v (color c))
  (hedge : ∀ v w, R v w → ∀ t, ∃ c, I v c ∧ I w c ∧ color c = t)

include hlocal hedge in
theorem local_permutations_eq_of_edge (v w : V) (h : R v w) : sigma v = sigma w := by
  apply Equiv.ext
  intro t
  obtain ⟨c, hvc, hwc, hc⟩ := hedge v w h t
  have hv := hlocal v c hvc
  have hw := hlocal w c hwc
  rw [hc] at hv hw
  exact hv.symm.trans hw

include hlocal hedge in
theorem local_permutations_eq_of_path (v w : V) (h : Relation.ReflTransGen R v w) :
    sigma v = sigma w := by
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    exact ih.trans (local_permutations_eq_of_edge R I color f sigma hlocal hedge b c hbc)

include hlocal hedge in
theorem single_global_type_permutation (hconnected : ∀ v w, Relation.ReflTransGen R v w)
    (hcover : ∀ c, ∃ v, I v c) (v0 : V) :
    ∀ c, color (f c) = sigma v0 (color c) := by
  intro c
  obtain ⟨v, hvc⟩ := hcover c
  have he := local_permutations_eq_of_path R I color f sigma hlocal hedge v v0 (hconnected v v0)
  exact (hlocal v c hvc).trans (congrArg (fun s : Equiv.Perm T => s (color c)) he)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4TypeCoherence
