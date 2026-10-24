import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeParabolicRootIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionDiagonalResidual
import SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups

/-! The literal opposite candidates ARE the minimal strict overgroups
of N(V). Actual opposition transports the proved positive family. Its
conjugation of each Weyl generator differs from that same generator by
an actual diagonal element, which belongs to N(V). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeMinimalParabolics
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourBorelIntersection
open CFSGReeFFourOppositeBorelFactors CFSGReeFFourMinimalParabolics
open CFSGReeFFourOppositeParabolicRootIntersection CFSGReeFFourOppositionDiagonalResidual
open CFSGReeFFourOppositionFixedPositiveNegative CFSGSurjectiveMinimalOvergroups

theorem simpleParabolic_opposition_map (m : ℕ) (b : Bool) :
    (simpleParabolic m b).map (MulAut.conj (oppositionFixed m)).toMonoidHom=
      negativeSimpleParabolic m b := by
  let e := MulAut.conj (oppositionFixed m)
  let d := oppositionFixed m*simpleWeyl m b*(oppositionFixed m)⁻¹*(simpleWeyl m b)⁻¹
  have hd : d∈oppositeBorel m :=
    diagonal_le_oppositeBorel m (opposition_simple_residual_mem_diagonal m b)
  have hval : d*simpleWeyl m b=e (simpleWeyl m b) := by
    dsimp only [d,e,MulAut.conj_apply]
    group
  have hw : simpleWeyl m b∈negativeSimpleParabolic m b :=
    (show Subgroup.closure {simpleWeyl m b}≤negativeSimpleParabolic m b from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
  have hB : (fixedBorel m).map e.toMonoidHom=oppositeBorel m := fixedBorel_opposition_map m
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sup_le
    · apply Subgroup.map_le_iff_le_comap.mp
      exact (le_of_eq hB).trans le_sup_left
    · apply (Subgroup.closure_le _).mpr
      apply Set.singleton_subset_iff.mpr
      change e (simpleWeyl m b)∈negativeSimpleParabolic m b
      rw [←hval]
      exact (negativeSimpleParabolic m b).mul_mem
        ((show oppositeBorel m≤negativeSimpleParabolic m b from le_sup_left) hd) hw
  · have hbase : oppositeBorel m≤(simpleParabolic m b).map e.toMonoidHom := by
      rw [←hB]
      exact Subgroup.map_mono (show fixedBorel m≤simpleParabolic m b from le_sup_left)
    apply sup_le hbase
    apply (Subgroup.closure_le _).mpr
    apply Set.singleton_subset_iff.mpr
    have hgen : e (simpleWeyl m b)∈(simpleParabolic m b).map e.toMonoidHom :=
      ⟨_,(show Subgroup.closure {simpleWeyl m b}≤simpleParabolic m b from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton _)),rfl⟩
    have hh := ((simpleParabolic m b).map e.toMonoidHom).mul_mem
      (((simpleParabolic m b).map e.toMonoidHom).inv_mem (hbase hd)) hgen
    rw [←hval,inv_mul_cancel_left] at hh
    exact hh

private theorem opposition_kernel_le_borel (m : ℕ) :
    (MulAut.conj (oppositionFixed m)).toMonoidHom.ker≤fixedBorel m := by
  rw [(MonoidHom.ker_eq_bot_iff (MulAut.conj (oppositionFixed m)).toMonoidHom).mpr
    (MulAut.conj (oppositionFixed m)).injective]
  exact bot_le

theorem oppositeBorel_lt_negativeSimpleParabolic (m : ℕ) (b : Bool) :
    oppositeBorel m<negativeSimpleParabolic m b := by
  have h := map_lt_map_of_kernel_le (MulAut.conj (oppositionFixed m)).toMonoidHom
    (opposition_kernel_le_borel m) (borel_lt_simpleParabolic m b)
  rw [fixedBorel_opposition_map,simpleParabolic_opposition_map] at h
  exact h

theorem negativeSimpleParabolic_minimal (m : ℕ) (b : Bool)
    (H : Subgroup (originalModelFixed m)) (hBH : oppositeBorel m<H)
    (hHP : H≤negativeSimpleParabolic m b) : H=negativeSimpleParabolic m b := by
  have hmin := map_minimal_overgroup (MulAut.conj (oppositionFixed m)).toMonoidHom
    (MulAut.conj (oppositionFixed m)).surjective (opposition_kernel_le_borel m)
    (borel_lt_simpleParabolic m b) (simpleParabolic_minimal m b)
  rw [fixedBorel_opposition_map,simpleParabolic_opposition_map] at hmin
  exact hmin H hBH hHP

theorem minimal_overgroup_eq_negativeSimpleParabolic (m : ℕ)
    (H : Subgroup (originalModelFixed m)) (hBH : oppositeBorel m<H)
    (hmin : ∀M : Subgroup (originalModelFixed m),oppositeBorel m<M→M≤H→M=H) :
    ∃b : Bool,H=negativeSimpleParabolic m b := by
  have hcover := minimal_overgroup_family_surjective
    (MulAut.conj (oppositionFixed m)).toMonoidHom
    (MulAut.conj (oppositionFixed m)).surjective (opposition_kernel_le_borel m)
    (simpleParabolic m) (minimal_overgroup_eq_simpleParabolic m)
  rw [fixedBorel_opposition_map] at hcover
  obtain ⟨b,hb⟩ := hcover H hBH hmin
  exact ⟨b,hb.trans (simpleParabolic_opposition_map m b)⟩

theorem negativeSimpleParabolic_injective (m : ℕ) :
    Function.Injective (negativeSimpleParabolic m) := by
  have hi := map_family_injective (MulAut.conj (oppositionFixed m)).toMonoidHom
    (opposition_kernel_le_borel m) (simpleParabolic m)
    (fun b=>show fixedBorel m≤simpleParabolic m b from le_sup_left) (simpleParabolic_injective m)
  intro b c he
  apply hi
  simpa only [simpleParabolic_opposition_map] using he

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeMinimalParabolics
