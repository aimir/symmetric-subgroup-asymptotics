import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter

/-! The actual elementary symplectic central quotient is nontrivial:
a literal terminal root transvection is nonscalar by its unit
off-diagonal entry. No cardinality or classical identification is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem elementaryProjective_nontrivial (K : Type*) [Field K] (r : ℕ) :
    Nontrivial (elementaryProjective K (r + 1)) := by
  let i := Fin.last r
  let u : elementaryRootGroup K (r + 1) :=
    ⟨rootTransvection K (r + 1) false i 1,
      rootTransvection_mem K (r + 1) false i 1⟩
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  apply nontrivial_of_ne (q u) 1
  intro h
  have hu : u ∈ Subgroup.center (elementaryRootGroup K (r + 1)) :=
    (QuotientGroup.eq_one_iff u).mp h
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r u).mp hu
  have he := congrArg (fun M : Mat K (r + 1) => M (Sum.inl i) (Sum.inr i)) hc
  have h10 : (1 : K) = 0 := by
    simpa [u, rootTransvection_val, rootMatrix, positive, i, Matrix.single,
      Matrix.one_apply] using he
  exact one_ne_zero h10

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
