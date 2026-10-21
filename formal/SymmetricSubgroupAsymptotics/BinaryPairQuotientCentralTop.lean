import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter

/-! A zero-top-image original denominator makes the top image of every
quotient-central original element central in the same actual top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem quotient_central_top_mem_center
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (u : U) (hu : QuotientGroup.mk' N u∈Subgroup.center (U ⧸ N)) :
    F.top.rangeRestrict u∈Subgroup.center F.top.range := by
  let q : U ⧸ N →* F.top.range := QuotientGroup.lift N F.top.rangeRestrict
    (by simpa only [MonoidHom.ker_rangeRestrict] using hN)
  apply Subgroup.mem_center_iff.mpr
  intro t
  obtain ⟨g,rfl⟩ := F.top.rangeRestrict_surjective t
  have he := congrArg q ((Subgroup.mem_center_iff.mp hu) (QuotientGroup.mk' N g))
  simpa only [map_mul] using he
end SymmetricSubgroupAsymptotics.BinaryPairFrame
