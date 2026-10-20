import SymmetricSubgroupAsymptotics.BinaryPairAxisRelativeRadical

/-! The intrinsic coinvariant radical of a physical axis is exactly the
coordinate space of the original whole-ambient relative radical. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w)) (B : Subgroup U) [B.Normal]
  (hB : B ≤ F.top.ker)

include hB

theorem ambientAxis_radical_eq_coinvariants_radical :
    F.ambientAxis (primeRelativeRadical 2 B) =
      (Representation.Coinvariants.ker (F.axisSubrepresentation B).toRepresentation).map
        (F.axisSubrepresentation B).toSubmodule.subtype := by
  ext v
  constructor
  · intro hv
    obtain ⟨k, hk, he⟩ := (F.mem_ambientAxis (primeRelativeRadical 2 B) v).mp hv
    have hkB : k.val ∈ B := primeRelativeRadical_le 2 B hk
    exact he ▸ (F.axis_mem_radical_iff B hB k hkB).mp hk
  · rintro ⟨a, ha, he⟩
    obtain ⟨k, hkB, hk⟩ := (F.mem_ambientAxis B a.val).mp a.property
    have hkm : F.bits k ∈
        (Representation.Coinvariants.ker (F.axisSubrepresentation B).toRepresentation).map
          (F.axisSubrepresentation B).toSubmodule.subtype := ⟨a, ha, hk.symm⟩
    exact (F.mem_ambientAxis (primeRelativeRadical 2 B) v).mpr
      ⟨k, (F.axis_mem_radical_iff B hB k hkB).mpr hkm, hk.trans he⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
