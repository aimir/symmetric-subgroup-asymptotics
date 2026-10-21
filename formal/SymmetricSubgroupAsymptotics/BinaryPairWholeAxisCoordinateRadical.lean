import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! Exact coordinate radical membership for the same original pair
kernel. Both directions follow from the intrinsic axis radical and an
injective coordinate change; no subgroup is enlarged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w n : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem bits_mem_coordinate_radical_iff
    (E : (Fin w → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (R : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hrad : ((Representation.Coinvariants.ker
      (F.axisNaturalSubrepresentation F.top.ker).toRepresentation).map
        (F.axisNaturalSubrepresentation F.top.ker).toSubmodule.subtype).map E.toLinearMap = R)
    (k : F.top.ker) :
    E (F.bits k) ∈ R ↔ (k : U) ∈ primeRelativeRadical 2 F.top.ker := by
  have he : (F.ambientAxis (primeRelativeRadical 2 F.top.ker)).map E.toLinearMap = R := by
    rw [F.axisNatural_radical F.top.ker le_rfl]
    exact hrad
  rw [← he]
  constructor
  · rintro ⟨v, hv, hvk⟩
    have hval : v = F.bits k := E.injective hvk
    rw [hval] at hv
    exact (F.bits_mem_ambientAxis (primeRelativeRadical 2 F.top.ker) k).mp hv
  · intro hk
    exact ⟨F.bits k, (F.bits_mem_ambientAxis (primeRelativeRadical 2 F.top.ker) k).mpr hk, rfl⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
