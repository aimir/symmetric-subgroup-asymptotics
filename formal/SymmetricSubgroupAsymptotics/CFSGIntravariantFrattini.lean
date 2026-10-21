import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The Frattini step for soluble-generation reductions

An automorphism-invariant conjugacy class is weaker than a characteristic
subgroup. The actual subgroup and its ambient embedding are retained here.
The resulting normalizer supplement is the structural step used to lift
simple-group soluble-generation witnesses to arbitrary finite groups.
No classification, finiteness or solvability input is needed for this step.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

/-- Every automorphic image is an actual inner conjugate. -/
def Intravariant {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ a : MulAut G, ∃ g : G,
    H.map a.toMonoidHom = H.map (MulAut.conj g).toMonoidHom

/-- Ambient conjugation changes `H` only by a conjugation from `E`. -/
def IntravariantIn {G : Type*} [Group G] (H E : Subgroup G) : Prop :=
  ∀ g : G, ∃ e : G, e ∈ E ∧
    H.map (MulAut.conj g).toMonoidHom = H.map (MulAut.conj e).toMonoidHom

theorem mem_normalizer_of_conjugation_map_eq {G : Type*} [Group G]
    (H : Subgroup G) (g : G)
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer H := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun K : Subgroup G => (K : Set G)) h

/-- The abstract Frattini argument uses invariance of the conjugacy class,
not pointwise invariance of the subgroup. -/
theorem normalizer_sup_eq_top_of_intravariantIn {G : Type*} [Group G]
    (H E : Subgroup G) (h : IntravariantIn H E) : Subgroup.normalizer H ⊔ E = ⊤ := by
  apply top_le_iff.mp
  intro g _
  obtain ⟨e, he, hconj⟩ := h g
  have hcomp : (MulAut.conj e⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (e⁻¹ * g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hid : (MulAut.conj e⁻¹).toMonoidHom.comp (MulAut.conj e).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : H.map (MulAut.conj (e⁻¹ * g)).toMonoidHom = H := by
    calc
      H.map (MulAut.conj (e⁻¹ * g)).toMonoidHom =
          H.map ((MulAut.conj e⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) :=
        congrArg (fun f : G →* G => H.map f) hcomp.symm
      _ = (H.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj e⁻¹).toMonoidHom :=
        (Subgroup.map_map H (MulAut.conj e⁻¹).toMonoidHom
          (MulAut.conj g).toMonoidHom).symm
      _ = (H.map (MulAut.conj e).toMonoidHom).map
          (MulAut.conj e⁻¹).toMonoidHom :=
        congrArg (fun L : Subgroup G => L.map (MulAut.conj e⁻¹).toMonoidHom) hconj
      _ = H.map ((MulAut.conj e⁻¹).toMonoidHom.comp (MulAut.conj e).toMonoidHom) :=
        Subgroup.map_map H (MulAut.conj e⁻¹).toMonoidHom (MulAut.conj e).toMonoidHom
      _ = H.map (MonoidHom.id G) := congrArg (fun f : G →* G => H.map f) hid
      _ = H := Subgroup.map_id H
  have hn : e⁻¹ * g ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_of_conjugation_map_eq H (e⁻¹ * g) hmap
  have hmem : e * (e⁻¹ * g) ∈ E ⊔ Subgroup.normalizer (H : Set G) :=
    Subgroup.mul_mem_sup he hn
  simpa only [mul_inv_cancel_left, sup_comm E (Subgroup.normalizer (H : Set G))]
    using hmem

/-- Intravariance inside a normal subgroup produces the actual ambient
Frattini witness after the original subtype embedding. -/
theorem intravariantIn_map_subtype {G : Type*} [Group G]
    (E : Subgroup G) [E.Normal] (H : Subgroup E) (hH : Intravariant H) :
    IntravariantIn (H.map E.subtype) E := by
  intro g
  obtain ⟨e, he⟩ := hH (MulAut.conjNormal g)
  refine ⟨e, e.property, ?_⟩
  calc
    _ = (H.map (MulAut.conjNormal g).toMonoidHom).map E.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    _ = (H.map (MulAut.conj e).toMonoidHom).map E.subtype :=
      congrArg (fun K : Subgroup E => K.map E.subtype) he
    _ = _ := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl

theorem normalizer_map_subtype_sup_eq_top {G : Type*} [Group G]
    (E : Subgroup G) [E.Normal] (H : Subgroup E) (hH : Intravariant H) :
    Subgroup.normalizer (H.map E.subtype) ⊔ E = ⊤ :=
  normalizer_sup_eq_top_of_intravariantIn _ _ (intravariantIn_map_subtype E H hH)

end SymmetricSubgroupAsymptotics.CFSGReduction
