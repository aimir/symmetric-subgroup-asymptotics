import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGTypeAIndexReindex

/-! A stronger actual D root-star subgroup. The fixed-centre SL root
space is embedded by simultaneous coordinate reindexing and the literal
D double embedding. Faithfulness pulls a central-image condition back
to the SAME SL group, proving injectivity after the D centre quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarSubgroup
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTypeAProjectivePointRoots CFSGTypeAColumnFormCoordinates CFSGTypeAIndexReindex
open CFSGTypeABlockEmbedding
variable (K : Type) [Field K]

abbrev StarCoordinates (s : ℕ) := Unit ⊕ Fin (s + 3)
abbrev StarSL (s : ℕ) := Matrix.SpecialLinearGroup (StarCoordinates s) K
abbrev StarForms (s : ℕ) := pointForms (firstVector (F := K) (n := Fin (s + 3)))

local instance orthogonalDIndexStarParameterCommGroup (s : ℕ) :
    CommGroup (Multiplicative (StarForms K s)) := inferInstance

def starEmbedding (s : ℕ) : StarSL K s →* elementaryRootGroup K (s + 4) :=
  (doubleIntoElementary K (s + 4)).comp
    (slReindex (F := K) (splitCoordinates (s + 3))).toMonoidHom

theorem doubleIntoElementary_injective (r : ℕ) : Function.Injective (doubleIntoElementary K r) := by
  intro A B h
  have hm := congrArg (fun u : elementaryRootGroup K r =>
    Matrix.toBlocks₁₁ (u.val : Mat K r)) h
  change A.val = B.val at hm
  exact Subtype.ext hm

theorem starEmbedding_injective (s : ℕ) : Function.Injective (starEmbedding K s) :=
  (doubleIntoElementary_injective K (s + 4)).comp
    (slReindex (F := K) (splitCoordinates (s + 3))).injective

theorem firstVector_ne_zero (s : ℕ) :
    (firstVector (F := K) (n := Fin (s + 3))) ≠ 0 := by
  intro he
  have h := congrArg (fun v : StarCoordinates s → K => v (Sum.inl ())) he
  simp only [firstVector, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at h

def starHom (s : ℕ) : Multiplicative (StarForms K s) →* elementaryProjective K (s + 4) :=
  ((QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))).comp
    (starEmbedding K s)).comp (pointRootSLHom (firstVector (F := K) (n := Fin (s + 3))))

theorem starHom_injective (s : ℕ) : Function.Injective (starHom K s) := by
  apply (MonoidHom.ker_eq_bot_iff (starHom K s)).mp
  apply bot_unique
  intro f hf
  have hc : starEmbedding K s (pointRootSLHom firstVector f) ∈
      Subgroup.center (elementaryRootGroup K (s + 4)) :=
    (QuotientGroup.eq_one_iff _).mp hf
  have hsource : pointRootSLHom firstVector f ∈ Subgroup.center (StarSL K s) := by
    apply Subgroup.mem_center_iff.mpr
    intro A
    apply starEmbedding_injective K s
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hc) (starEmbedding K s A)
  have he := pointRootSL_eq_one_of_mem_center (firstVector_ne_zero K s) f hsource
  have hp : pointRootHom firstVector f = 1 := by
    change projection (pointRootSLHom firstVector f) = 1
    rw [he, map_one]
  exact (Subgroup.mem_bot).mpr
    (pointRootHom_injective (firstVector_ne_zero K s) (hp.trans (map_one (pointRootHom firstVector)).symm))

def starRoot (s : ℕ) : Subgroup (elementaryProjective K (s + 4)) := (starHom K s).range

def starRootEquiv (s : ℕ) : Multiplicative (StarForms K s) ≃* starRoot K s :=
  MonoidHom.ofInjective (starHom_injective K s)

theorem starRoot_card (s : ℕ) : Nat.card (starRoot K s) = Nat.card K ^ (s + 3) := by
  calc
    Nat.card (starRoot K s) = Nat.card (Multiplicative (StarForms K s)) :=
      Nat.card_congr (starRootEquiv K s).symm.toEquiv
    _ = Nat.card (pointRoot (firstVector (F := K) (n := Fin (s + 3)))) :=
      Nat.card_congr (pointRootEquiv (firstVector_ne_zero K s)).toEquiv
    _ = _ := by
      rw [pointRoot_card (firstVector_ne_zero K s), Fintype.card_sum, Fintype.card_unit,
        Fintype.card_fin]
      congr 1
      omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarSubgroup
