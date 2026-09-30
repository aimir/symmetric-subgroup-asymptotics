import SymmetricSubgroupAsymptotics.BinaryCarrierRoutedProfileAxisClosure

/-!
# Recovery from one complete physical orbit chart

Once the complete simultaneous point chart is fixed, the abstract full
product source loses no information about the original labelled permutation
subgroup.  The inverse first undoes the flattening equivalence, maps the
product source through the faithful independent orbit action, and finally
returns along the fixed point chart.

This is the source-extraction statement needed inside one aligned carrier
key.  It deliberately takes the complete chart as fixed data: a finite route
tag or a table containing only changed blocks does not by itself determine
the embeddings of the unchanged literal orbits.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalChartRecovery

open SymmetricSubgroupAsymptotics
open BinaryCarrierRoutedProfileAxisClosure

variable {ι X : Type} [Fintype ι] [DecidableEq ι]
  (Ω : ι → Type) [∀ i, Fintype (Ω i)]
  (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
  (m : ι → ℕ)
  (e : OrbitProfilePoints Ω m ≃ X)

/-- Actual labelled permutation subgroups which are full on one fixed
complete orbit chart. -/
abbrev FixedChartFamily :=
  {H : Subgroup (Equiv.Perm X) // OrbitProfileFullOn U e H}

/-- Move an actual subgroup back to the fixed abstract profile point set. -/
def model (H : FixedChartFamily Ω U m e) :
    Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) :=
  relabelSubgroup e.symm H.1

theorem model_full (H : FixedChartFamily Ω U m e) :
    OrbitProfileFull U 1 (model Ω U m e H) := by
  have h := H.2.relabel e.symm
  apply (orbitProfileFullOn_iff U (Equiv.refl _) (model Ω U m e H)).mp
  simpa only [Equiv.self_trans_symm] using h

/-- The complete correlated subgroup of the fixed product of orbit actions. -/
def profileSource (H : FixedChartFamily Ω U m e) :
    Subgroup (OrbitProfileProductGroup m U) :=
  (model Ω U m e H).comap (orbitProfileProductAction m U)

/-- Flatten the curried profile product to one coordinate per occurrence. -/
def source (H : FixedChartFamily Ω U m e) :
    Subgroup (FlatGroup Ω U m) :=
  (profileSource Ω U m e H).map (flatten Ω U m).toMonoidHom

/-- Decode a flat occurrence source using the same complete physical chart. -/
def recover (J : Subgroup (FlatGroup Ω U m)) :
    Subgroup (Equiv.Perm X) :=
  relabelSubgroup e
    ((J.comap (flatten Ω U m).toMonoidHom).map
      (orbitProfileProductAction m U))

/-- Mapping through the fixed chart, product action, and flattening and then
undoing those maps returns the original labelled subgroup. -/
theorem recover_source (H : FixedChartFamily Ω U m e) :
    recover Ω U m e (source Ω U m e H) = H.1 := by
  unfold recover source profileSource
  rw [Subgroup.comap_map_eq_self_of_injective
    (f := (flatten Ω U m).toMonoidHom) (flatten Ω U m).injective]
  rw [Subgroup.map_comap_eq_self
    (orbitProfileFull_le_product_range (model_full Ω U m e H))]
  simpa only [model] using relabelSubgroup_symm e.symm H.1

/-- On a fixed complete chart the flat abstract source is injective. -/
theorem source_injective :
    Function.Injective (source Ω U m e) := by
  intro H K h
  apply Subtype.ext
  calc
    H.1 = recover Ω U m e (source Ω U m e H) :=
      (recover_source Ω U m e H).symm
    _ = recover Ω U m e (source Ω U m e K) := congrArg (recover Ω U m e) h
    _ = K.1 := recover_source Ω U m e K

end SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalChartRecovery

end
