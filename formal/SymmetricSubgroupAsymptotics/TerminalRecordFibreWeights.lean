import SymmetricSubgroupAsymptotics.TerminalIncidenceSum
import SymmetricSubgroupAsymptotics.TerminalRankRecords
import SymmetricSubgroupAsymptotics.TerminalPullbackFibres
import SymmetricSubgroupAsymptotics.BinaryCharacterProducts

/-! Exact original image fibres and all central-fibre weights of their records. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite
variable {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
  (u : ℕ) (T : Type) [Group T] [Finite T]

/-- The complete central fibre of the literal record pullback has exactly
the original annihilator weight, including every relation subspace. -/
theorem terminalCriticalPullback_card
    (p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] CriticalProductSpace a s) :
    (Nat.card {L : Subgroup (terminalPullbackGroup (criticalProductQuotient a s)
      (terminalCriticalRecordHom a s (terminalExteriorMap T) p)) //
        L.map (terminalPullbackProjection (criticalProductQuotient a s)
          (terminalCriticalRecordHom a s (terminalExteriorMap T) p))=⊤} : ℝ) =
      terminalCriticalMapWeight a s u T p := by
  let π := terminalPullbackProjection (criticalProductQuotient a s)
    (terminalCriticalRecordHom a s (terminalExteriorMap T) p)
  let e := terminalPullbackKernelChart (criticalProductQuotient a s)
    (criticalProductKernelChart a s) (terminalCriticalRecordHom a s (terminalExteriorMap T) p)
  have hπ : Function.Surjective π := terminalPullbackProjection_surjective _ _
    (terminalCriticalSection a s) (terminalCriticalSection_projection a s)
  have hc : π.ker ≤ Subgroup.center _ := terminalPullbackProjection_ker_central _ _
    (criticalProductQuotient_ker_central a s)
  have h : (Nat.card {L : Subgroup (terminalPullbackGroup (criticalProductQuotient a s)
      (terminalCriticalRecordHom a s (terminalExteriorMap T) p)) // L.map π=⊤} : ℝ) =
      ∑ L : {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ι → ZMod 2)) //
        L ≤ terminalSplittingAnnihilator π e},
        (2 : ℝ)^(binaryCharacterRank (Multiplicative (Fin u → ZMod 2) × T)*
          Module.finrank (ZMod 2) L.1) := by
    exact_mod_cast terminal_all_lifts_count_annihilator π e hπ hc
  rw [h,binaryCharacterRank_multiplicative_prod,Module.finrank_pi,Fintype.card_fin]
  exact terminal_annihilator_weight_reindex _ _

/-- Express a raw original-basis quotient record in the fixed physical
translation/shear coordinates. This is an actual linear isomorphism. -/
def terminalRecordPhysicalMap
    (p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
      (Fin (criticalProductRank a s) → ZMod 2)) :
    ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] CriticalProductSpace a s :=
  (criticalProductChart a s).toLinearMap.comp p

omit [Finite T] in
theorem terminalRecordPhysicalMap_hom
    (p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
      (Fin (criticalProductRank a s) → ZMod 2)) :
    terminalCriticalRecordHom a s (terminalExteriorMap T) (terminalRecordPhysicalMap a s u T p) =
      (MonoidHom.fst _ T).comp (terminalRawRecordGroupMap u p) := by
  apply MonoidHom.ext
  intro x
  change Multiplicative.ofAdd ((criticalProductChart a s).symm
    (criticalProductChart a s (p (x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2))))) = _
  rw [(criticalProductChart a s).symm_apply_apply]
  rfl

/-- Original subgroup fibre equality for each original ordered record. The
record is injective on its vertical coordinates, so no group fibre is lost. -/
theorem terminalOriginalRecordFibre_card
    (p : TerminalOrderedMaps (A := BinaryAbelianization T)
      (V := Fin (criticalProductRank a s) → ZMod 2) u) :
    (Nat.card {H : Subgroup (CriticalProductGroup a s × T) //
      H.map (terminalProductImageMap (T := T) (criticalProductQuotient a s)) =
        (terminalRawRecordGroupMap u p.1).range} : ℝ) =
      terminalCriticalMapWeight a s u T (terminalRecordPhysicalMap a s u T p.1) := by
  rw [terminalPullbackImageFibre_card _ _ (terminalRawRecordGroupMap_injective u p)]
  rw [← terminalRecordPhysicalMap_hom a s u T p.1]
  exact terminalCriticalPullback_card a s u T _

end SymmetricSubgroupAsymptotics
