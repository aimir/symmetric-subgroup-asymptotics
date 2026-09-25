import SymmetricSubgroupAsymptotics.CriticalProducts
import SymmetricSubgroupAsymptotics.CriticalProfileAssembly

/-! Indexed original-action groups transported to the concrete binary product. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

def CriticalLocalGroup : CriticalActionKind → Type
  | .c2 => Multiplicative (Fin 1 → ZMod 2)
  | .v4 => Multiplicative (Fin 2 → ZMod 2)
  | .d8 => BinaryHeisenberg 1
  | .e8 => BinaryHeisenberg 2

instance (i : CriticalActionKind) : Group (CriticalLocalGroup i) := by
  cases i <;> dsimp [CriticalLocalGroup] <;> infer_instance

/-- Each literal permutation range is identified with its faithful coordinates. -/
def criticalLocalEquiv (i : CriticalActionKind) : CriticalLocalGroup i ≃* criticalActionSubgroup i := by
  cases i
  · exact MonoidHom.ofInjective (regularBinaryAction_injective 1)
  · exact MonoidHom.ofInjective (regularBinaryAction_injective 2)
  · exact MonoidHom.ofInjective (BinaryHeisenberg.action_injective 1)
  · exact MonoidHom.ofInjective (BinaryHeisenberg.action_injective 2)

def CriticalProfile.abelianRank (p : CriticalProfile) : ℕ := p.c2 + 2 * p.v4

abbrev CriticalProfileAbelianSpace (p : CriticalProfile) :=
  (Fin p.c2 → Fin 1 → ZMod 2) × (Fin p.v4 → Fin 2 → ZMod 2)

def criticalProfileAbelianChart (p : CriticalProfile) :
    (Fin p.abelianRank → ZMod 2) ≃ₗ[ZMod 2] CriticalProfileAbelianSpace p :=
  LinearEquiv.ofFinrankEq (R := ZMod 2) _ _ (by
    rw [Module.finrank_pi, Fintype.card_fin]
    simp [CriticalProfileAbelianSpace, CriticalProfile.abelianRank,
      Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm])

abbrev CriticalProfileNonabelianIndex (p : CriticalProfile) := Fin p.d8 ⊕ Fin p.e8

def criticalProfileNonabelianChoice (p : CriticalProfile) : CriticalProfileNonabelianIndex p → Bool :=
  Sum.elim (fun _ ↦ false) (fun _ ↦ true)

abbrev CriticalProfileCoordinateGroup (p : CriticalProfile) :=
  CriticalProductGroup p.abelianRank (criticalProfileNonabelianChoice p)

/-- Regrouping retains every original occurrence and the two coordinates of
each V4 occurrence together. No fullness condition is imposed on separate bits. -/
def criticalProfileProductEquiv (p : CriticalProfile) :
    OrbitProfileProductGroup p.multiplicity criticalActionSubgroup ≃*
      CriticalProfileCoordinateGroup p where
  toFun g :=
    (Multiplicative.ofAdd ((criticalProfileAbelianChart p).symm
      (fun j ↦ ((criticalLocalEquiv .c2).symm (g .c2 j)).toAdd,
       fun j ↦ ((criticalLocalEquiv .v4).symm (g .v4 j)).toAdd)),
     fun i ↦ match i with
       | .inl j => (criticalLocalEquiv .d8).symm (g .d8 j)
       | .inr j => (criticalLocalEquiv .e8).symm (g .e8 j))
  invFun g := fun i ↦ match i with
    | .c2 => fun j ↦ criticalLocalEquiv .c2 (Multiplicative.ofAdd
        ((criticalProfileAbelianChart p g.1.toAdd).1 j))
    | .v4 => fun j ↦ criticalLocalEquiv .v4 (Multiplicative.ofAdd
        ((criticalProfileAbelianChart p g.1.toAdd).2 j))
    | .d8 => fun j ↦ criticalLocalEquiv .d8 (g.2 (.inl j))
    | .e8 => fun j ↦ criticalLocalEquiv .e8 (g.2 (.inr j))
  left_inv g := by
    funext i j
    cases i <;> simp
  right_inv g := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change (criticalProfileAbelianChart p).symm _ = g.1.toAdd
      simp
    · funext i
      cases i <;> simp
  map_mul' g h := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change (criticalProfileAbelianChart p).symm _ =
        (criticalProfileAbelianChart p).symm _ + (criticalProfileAbelianChart p).symm _
      rw [← (criticalProfileAbelianChart p).symm.map_add]
      apply congrArg (criticalProfileAbelianChart p).symm
      apply Prod.ext <;> funext j <;> simp <;> rfl
    · funext i
      cases i <;> simp <;> rfl

def CriticalProfileCoordinateFull (p : CriticalProfile)
    (H : Subgroup (CriticalProfileCoordinateGroup p)) : Prop :=
  OrbitProfileProductFull p.multiplicity criticalActionSubgroup
    (H.comap (criticalProfileProductEquiv p).toMonoidHom)

/-- Actual full model subgroups transported by a fully instantiated group
equivalence; subgroup values are mapped bijectively. -/
def criticalModelSubgroupsEquivCoordinates (p : CriticalProfile) :
    CriticalModelSubgroups p ≃
      {H : Subgroup (CriticalProfileCoordinateGroup p) // CriticalProfileCoordinateFull p H} :=
  (criticalModelSubgroupsEquivProduct p).trans
    { toFun := fun H ↦ ⟨H.1.map (criticalProfileProductEquiv p).toMonoidHom, by
        change OrbitProfileProductFull _ _ _
        rw [Subgroup.comap_map_eq_self_of_injective (criticalProfileProductEquiv p).injective]
        exact H.2⟩
      invFun := fun H ↦ ⟨H.1.comap (criticalProfileProductEquiv p).toMonoidHom, H.2⟩
      left_inv := fun H ↦ Subtype.ext
        (Subgroup.comap_map_eq_self_of_injective (criticalProfileProductEquiv p).injective H.1)
      right_inv := fun H ↦ Subtype.ext
        (Subgroup.map_comap_eq_self_of_surjective (criticalProfileProductEquiv p).surjective H.1) }

theorem criticalProfileCoordinateFull_nonabelian (p : CriticalProfile)
    (H : Subgroup (CriticalProfileCoordinateGroup p)) (hH : CriticalProfileCoordinateFull p H)
    (i : CriticalProfileNonabelianIndex p) :
    H.map (criticalProductFactorProjection p.abelianRank (criticalProfileNonabelianChoice p) i) = ⊤ := by
  apply top_unique
  intro u _
  cases i with
  | inl j =>
    obtain ⟨g, hg⟩ := hH .d8 j (criticalLocalEquiv .d8 u)
    refine ⟨criticalProfileProductEquiv p g.1, g.2, ?_⟩
    change (criticalLocalEquiv .d8).symm (g.1 .d8 j) = u
    rw [hg]
    exact (criticalLocalEquiv .d8).symm_apply_apply u
  | inr j =>
    obtain ⟨g, hg⟩ := hH .e8 j (criticalLocalEquiv .e8 u)
    refine ⟨criticalProfileProductEquiv p g.1, g.2, ?_⟩
    change (criticalLocalEquiv .e8).symm (g.1 .e8 j) = u
    rw [hg]
    exact (criticalLocalEquiv .e8).symm_apply_apply u

theorem criticalProfile_product_rank (p : CriticalProfile) :
    criticalProductRank p.abelianRank (criticalProfileNonabelianChoice p) = p.rank := by
  simp [criticalProductRank, criticalProfileNonabelianChoice, criticalFactorRank,
    CriticalProfile.abelianRank, CriticalProfile.rank, Fintype.sum_sum_type]
  omega

theorem criticalProfile_product_loss (p : CriticalProfile) :
    (criticalProductRank p.abelianRank (criticalProfileNonabelianChoice p) : ℝ) / 2 -
      Fintype.card (CriticalProfileNonabelianIndex p) = (p.c2 : ℝ) / 2 + p.v4 + p.e8 := by
  rw [criticalProfile_product_rank]
  simp [CriticalProfileNonabelianIndex, CriticalProfile.rank]
  ring

end SymmetricSubgroupAsymptotics
