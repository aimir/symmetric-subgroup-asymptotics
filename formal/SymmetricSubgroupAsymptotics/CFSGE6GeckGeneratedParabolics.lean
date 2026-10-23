import SymmetricSubgroupAsymptotics.CFSGE6GeckMinimalOvergroups
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootGeneratedPGroup

/-! Internal-J versions of the actual four minimal overgroups and the
literal positive normalizer. These are genuine subgroup equalities,
ready for passage through the original projective quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedParabolics
open CFSGE6GeckMinimalOvergroups CFSGE6GeckIntermediateOvergroup
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
local notation "J" => fixedRootGenerated K sigma

def upperGenerated : Subgroup J := (upperIn K J).subgroupOf J

def parabolicGenerated (a : Fin 4) : Subgroup J := (simpleParabolic K J a).subgroupOf J

theorem upperGenerated_map : (upperGenerated K sigma).map (J).subtype=upperIn K J :=
  Subgroup.map_subgroupOf_eq_of_le inf_le_right

theorem parabolicGenerated_map (a : Fin 4) :
    (parabolicGenerated K sigma a).map (J).subtype=simpleParabolic K J a :=
  Subgroup.map_subgroupOf_eq_of_le (simpleParabolic_le_intermediate K sigma J le_rfl a)

theorem upperGenerated_eq_normalizer :
    upperGenerated K sigma=Subgroup.normalizer (rootPart K sigma false : Set J) := by
  have hrange : signedFixed K sigma false≤(J).subtype.range := by
    rw [Subgroup.range_subtype]
    exact signedFixed_le_generated K sigma false
  have hn : (Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).comap (J).subtype=
      Subgroup.normalizer (rootPart K sigma false : Set J) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (f:=(J).subtype) hrange]
    rfl
  apply Subgroup.ext
  intro x
  change x.val∈upperIn K J↔x∈Subgroup.normalizer (rootPart K sigma false : Set J)
  rw [upperIn_eq_normalizer_inter K sigma J (fixedRootGenerated_le_preimage K sigma),←hn]
  change (x.val∈Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ) ∧
    x.val∈J)↔x.val∈Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)
  exact ⟨And.left,fun h=>⟨h,x.property⟩⟩

theorem upperGenerated_lt_parabolicGenerated (a : Fin 4) :
    upperGenerated K sigma<parabolicGenerated K sigma a := by
  apply (Subgroup.map_lt_map_iff_of_injective (J).subtype_injective).mp
  rw [upperGenerated_map,parabolicGenerated_map]
  exact upperIn_lt_simpleParabolic K J a

theorem parabolicGenerated_minimal (a : Fin 4) (H : Subgroup J)
    (hBH : upperGenerated K sigma<H) (hHP : H≤parabolicGenerated K sigma a) :
    H=parabolicGenerated K sigma a := by
  apply Subgroup.map_injective (f:=(J).subtype) (J).subtype_injective
  rw [parabolicGenerated_map]
  apply simpleParabolic_minimal K sigma J le_rfl (fixedRootGenerated_le_preimage K sigma) a
  · have hh := (Subgroup.map_lt_map_iff_of_injective (J).subtype_injective).mpr hBH
    rwa [upperGenerated_map] at hh
  · have hh := Subgroup.map_mono (f:=(J).subtype) hHP
    rwa [parabolicGenerated_map] at hh

theorem parabolicGenerated_injective : Function.Injective (parabolicGenerated K sigma) := by
  intro a b he
  apply simpleParabolic_injective K J
  have hh := congrArg (fun P : Subgroup J=>P.map (J).subtype) he
  simpa only [parabolicGenerated_map] using hh

theorem exists_parabolicGenerated_le (H : Subgroup J) (hBH : upperGenerated K sigma<H) :
    ∃a : Fin 4,parabolicGenerated K sigma a≤H := by
  have hstrict := (Subgroup.map_lt_map_iff_of_injective (J).subtype_injective).mpr hBH
  rw [upperGenerated_map] at hstrict
  obtain ⟨a,ha⟩ := exists_simple_weyl_mem_of_upperIn_lt K sigma J (H.map (J).subtype)
    le_rfl (fixedRootGenerated_le_preimage K sigma) hstrict (Subgroup.map_subtype_le H)
  refine ⟨a,(Subgroup.map_le_map_iff_of_injective (J).subtype_injective).mp ?_⟩
  rw [parabolicGenerated_map]
  exact sup_le hstrict.le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ha))

end SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedParabolics
