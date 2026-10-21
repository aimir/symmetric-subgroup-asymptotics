import SymmetricSubgroupAsymptotics.C3HighSemisimplePhysicalCover

/-! Relabelling the complete physical subgroup retains the same actual
semisimple orbit/chart and leaves the untouched complement unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The retained chart makes the complete physical owner invariant under an
arbitrary relabelling.  No orbit representative or abstract isomorphism
class is chosen. -/
theorem c3PhysicalHighSemisimpleOwner_relabel_iff {m n : ℕ}
    (hmn : m = n) (e : Fin m ≃ Fin n)
    (G : Subgroup (Equiv.Perm (Fin m))) :
    C3PhysicalHighSemisimpleOwner n (relabelSubgroup e G) ↔
      C3PhysicalHighSemisimpleOwner m G := by
  subst n
  constructor
  · rintro ⟨b, c, H, hc, hfull, o, N, hN, hHigh, hOwner⟩
    refine ⟨b, c.trans e.symm, H, ?_, hfull, o, N, hN, hHigh, hOwner⟩
    calc
      relabelSubgroup (c.trans e.symm)
          (H.map (fusionOrbitAction ternaryRegularAction)) =
        relabelSubgroup e.symm
          (relabelSubgroup c
            (H.map (fusionOrbitAction ternaryRegularAction))) := by
              rw [relabelSubgroup_trans]
      _ = relabelSubgroup e.symm (relabelSubgroup e G) := by rw [hc]
      _ = G := relabelSubgroup_symm e G
  · rintro ⟨b, c, H, hc, hfull, o, N, hN, hHigh, hOwner⟩
    refine ⟨b, c.trans e, H, ?_, hfull, o, N, hN, hHigh, hOwner⟩
    calc
      relabelSubgroup (c.trans e)
          (H.map (fusionOrbitAction ternaryRegularAction)) =
        relabelSubgroup e
          (relabelSubgroup c
            (H.map (fusionOrbitAction ternaryRegularAction))) := by
              rw [relabelSubgroup_trans]
      _ = relabelSubgroup e G := by rw [hc]

end SymmetricSubgroupAsymptotics
