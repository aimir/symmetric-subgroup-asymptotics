import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-! Literal action conjugacy transports normal axes, quotients and weights. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] {H U : Subgroup G} (g : G)
  (h : MulAut.conj g • H = U)

/-- This equivalence is the original ambient conjugation on every element. -/
def actionConjugacyEquiv : H ≃* U :=
  (Subgroup.equivSMul (MulAut.conj g) H).trans (MulEquiv.subgroupCongr h)

@[simp] theorem actionConjugacyEquiv_coe (x : H) :
    (actionConjugacyEquiv g h x : G) = g*x*g⁻¹ := rfl

def actionConjugacyNormal (N : Subgroup H) : Subgroup U :=
  N.map (actionConjugacyEquiv g h).toMonoidHom

instance actionConjugacyNormal_normal (N : Subgroup H) [N.Normal] :
    (actionConjugacyNormal g h N).Normal :=
  Subgroup.Normal.map inferInstance _ (actionConjugacyEquiv g h).surjective

/-- Both the axis and the action are moved by the same literal permutation. -/
theorem actionConjugacyNormal_ambient (N : Subgroup H) :
    (actionConjugacyNormal g h N).map U.subtype =
      MulAut.conj g • (N.map H.subtype) := by
  rw [actionConjugacyNormal, Subgroup.pointwise_smul_def, Subgroup.map_map,
    Subgroup.map_map]
  rfl

/-- The quotient chart commutes with both original quotient maps. -/
def actionConjugacyQuotient (N : Subgroup H) [N.Normal] :
    H ⧸ N ≃* U ⧸ actionConjugacyNormal g h N :=
  QuotientGroup.congr N _ (actionConjugacyEquiv g h) rfl

@[simp] theorem actionConjugacyQuotient_mk (N : Subgroup H) [N.Normal] (x : H) :
    actionConjugacyQuotient g h N (QuotientGroup.mk' N x) =
      QuotientGroup.mk' (actionConjugacyNormal g h N) (actionConjugacyEquiv g h x) := rfl

include g h in
/-- Original action-normalizer weights are unchanged by the same ambient
conjugacy used by the finite registry. -/
theorem actionConjugacy_normalizer_card :
    Nat.card (Subgroup.normalizer (H : Set G)) =
      Nat.card (Subgroup.normalizer (U : Set G)) := by
  have he : MulAut.conj g • Subgroup.normalizer (H : Set G) =
      Subgroup.normalizer (U : Set G) := by
    change (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq]
    exact congrArg (fun V : Subgroup G => Subgroup.normalizer (V : Set G)) h
  exact Nat.card_congr ((Subgroup.equivSMul (MulAut.conj g)
    (Subgroup.normalizer (H : Set G))).trans (MulEquiv.subgroupCongr he)).toEquiv

/-- The two local registries jointly cover every actual action and every
literal normal in it; the witness retains the single ambient conjugation. -/
theorem pGroup_action_normal_registry_complete [Finite G]
    {p : ℕ} [Fact p.Prime] {I : Type*}
    (actions : I → Subgroup G) (hgroups : ∀ i, IsPGroup p (actions i))
    (P : Sylow p G) (root : I) (hroot : actions root = (P : Subgroup G))
    (A : Subgroup G → Prop)
    (hup : ∀ H K, H ≤ K → A H → A K)
    (hconj : ∀ (g : G) (H : Subgroup G), A H → A (MulAut.conj g • H))
    (hchildren : ∀ i, ∀ K : Subgroup G,
      K < actions i → K.relIndex (actions i) = p → A K →
        ActionRegistryCovered actions K)
    (normals : ∀ i, Set (Subgroup (actions i)))
    (hbot : ∀ i, ⊥ ∈ normals i)
    (hnormal : ∀ i N, N ∈ normals i → N.Normal)
    (hsteps : ∀ i N, N ∈ normals i → ∀ _hN : N.Normal, ∀ z : (actions i) ⧸ N,
      z ∈ Subgroup.center ((actions i) ⧸ N) → orderOf z = p →
      (Subgroup.zpowers z).comap (QuotientGroup.mk' N) ∈ normals i)
    (H : Subgroup G) (hH : IsPGroup p H) (hAH : A H)
    (N : Subgroup H) [N.Normal] :
    ∃ i : I, ∃ g : G, ∃ hg : MulAut.conj g • H = actions i,
      actionConjugacyNormal g hg N ∈ normals i := by
  obtain ⟨i,g,hg⟩ := pGroup_action_registry_complete actions P root hroot
    A hup hconj hchildren H hH hAH
  exact ⟨i,g,hg,pGroup_normal_registry_complete (hgroups i) (normals i)
    (hbot i) (hnormal i) (hsteps i) (actionConjugacyNormal g hg N)⟩

end SymmetricSubgroupAsymptotics
