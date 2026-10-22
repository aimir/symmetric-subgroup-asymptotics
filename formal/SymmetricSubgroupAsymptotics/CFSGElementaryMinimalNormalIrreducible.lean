import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.CFSGSurjectiveRepresentationIrreducible

/-! The actual quotient action on an elementary minimal normal subgroup is
irreducible. Invariant subspaces are transported back to literal ambient
normal subgroups; no model, catalogue or composition bound is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementaryMinimalNormalChart

variable {G : Type} [Group G] {E : Subgroup G} [E.Normal]
    (C : ElementaryMinimalNormalChart E)

private def invariantSubgroup
    (W : Subrepresentation C.quotientRepresentation.ρ) : Subgroup E :=
  W.toSubmodule.toAddSubgroup.toSubgroup.comap C.equiv.toMonoidHom

theorem quotientRepresentation_irreducible
    (hne : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E) :
    Representation.IsIrreducible C.quotientRepresentation.ρ := by
  letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hne
  letI : Nontrivial (Multiplicative C.V) := C.equiv.injective.nontrivial
  letI : Nontrivial C.V := Multiplicative.toAdd.injective.nontrivial
  let rho := C.quotientRepresentation.ρ
  have hbt : (⊥ : Subrepresentation rho) ≠ ⊤ := by
    obtain ⟨v,hv⟩ := exists_ne (0 : C.V)
    intro hh
    have hm : v ∈ (⊥ : Subrepresentation rho) := by rw [hh]; trivial
    exact hv ((Submodule.mem_bot (R := ZMod C.p)).mp hm)
  letI : Nontrivial (Subrepresentation rho) := ⟨⟨⊥,⊤,hbt⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let K0 : Subgroup E := C.invariantSubgroup W
  let K : Subgroup G := K0.map E.subtype
  have hKn : K.Normal := by
    constructor
    intro y hy g
    obtain ⟨e,he,rfl⟩ := hy
    have hact := W.apply_mem_toSubmodule (QuotientGroup.mk' E g) he
    change C.quotientRepresentation.ρ (QuotientGroup.mk' E g)
      (C.equiv e).toAdd ∈ W at hact
    rw [C.quotientRepresentation_apply] at hact
    exact ⟨MulAut.conjNormal g e,hact,rfl⟩
  have hle : K ≤ E := Subgroup.map_subtype_le K0
  have hK0 : K0 = ⊥ ∨ K0 = ⊤ := by
    rcases hmin K hKn hle with hbot | htop
    · exact Or.inl ((K0.map_eq_bot_iff_of_injective E.subtype_injective).mp hbot)
    · right
      apply Subgroup.map_injective E.subtype_injective
      simpa only [K, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  rcases hK0 with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    apply SetLike.ext
    intro v
    constructor
    · intro hv
      let e : E := C.equiv.symm (Multiplicative.ofAdd v)
      have he : e ∈ K0 := by
        change (C.equiv e).toAdd ∈ W
        simpa [e] using hv
      rw [hbot] at he
      have he1 : e = 1 := Subgroup.mem_bot.mp he
      have hv0 : v = 0 := by
        apply Multiplicative.ofAdd.injective
        calc
          Multiplicative.ofAdd v = C.equiv e := (C.equiv.apply_symm_apply _).symm
          _ = C.equiv 1 := congrArg C.equiv he1
          _ = Multiplicative.ofAdd 0 := by simp
      simp [hv0]
    · intro hv
      have hv0 : v = 0 := (Submodule.mem_bot (R := ZMod C.p)).mp hv
      rw [hv0]
      exact Submodule.zero_mem _
  · right
    apply Subrepresentation.toSubmodule_injective
    apply SetLike.ext
    intro v
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      let e : E := C.equiv.symm (Multiplicative.ofAdd v)
      have he : e ∈ K0 := by rw [htop]; exact Subgroup.mem_top e
      change (C.equiv e).toAdd ∈ W at he
      simpa [e] using he

end SymmetricSubgroupAsymptotics.ElementaryMinimalNormalChart
