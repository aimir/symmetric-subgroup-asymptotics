import SymmetricSubgroupAsymptotics.ZmudNormalDetection
import SymmetricSubgroupAsymptotics.ZmudTensorFixedSpaces
import SymmetricSubgroupAsymptotics.NonabelianSoclePartCenterless

/-! One irreducible complex representation detects all nonabelian ambient
minimal normal subgroups. Successive detectors are induced in the actual
quotient by the preceding selected socle, tensored, and then restricted to
an injected irreducible constituent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.ZmudNonabelianSocleDetection

open ZmudFixedSpaceConstituents

variable {G : Type} [Group G] [Finite G]

/-- Inflation retains the actual underlying nonzero finite space. -/
def inflate {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (E : Envelope Q) : Envelope G := {
  Space := E.Space
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  nontrivial := inferInstance
  action := E.action.comp f }

/-- Bundling an irreducible representation as a nonzero envelope. -/
def irreducibleEnvelope (r : FiniteIrreducibleRepresentation ℂ G) : Envelope G := by
  letI : Nontrivial r.action.asModule := IsSimpleModule.nontrivial ℂ[G] r.action.asModule
  letI : Nontrivial r.Space := r.action.asModuleEquiv.toEquiv.symm.nontrivial
  exact {
    Space := r.Space
    addCommGroup := inferInstance
    module := inferInstance
    finiteDimensional := inferInstance
    nontrivial := inferInstance
    action := r.action }

/-- Fixed-space exclusion passes to any actually injected constituent. -/
theorem fixedFree_of_injection
    (r : FiniteIrreducibleRepresentation ℂ G) (E : Envelope G)
    (j : r.action.IntertwiningMap E.action) (hj : Function.Injective j)
    (N : Subgroup G)
    (hfix : ∀ v : E.Space, (∀ n : N, E.action n.1 v = v) → v = 0) :
    ∀ v : r.Space, (∀ n : N, r.action n.1 v = v) → v = 0 := by
  intro v hv
  apply hj
  change j.toLinearMap v = j.toLinearMap 0
  rw [map_zero]
  apply hfix
  intro n
  have he := Representation.IntertwiningMap.isIntertwining
    r.action E.action j n.1 v
  rw [hv n] at he
  exact he.symm

omit [Finite G] in
private theorem minimal_kernel_inf_eq_bot
    (r : FiniteIrreducibleRepresentation ℂ G)
    (N : Subgroup G) (hN : IsMinimalNormalSubgroup N)
    (hfix : ∀ v : r.Space, (∀ n : N, r.action n.1 v = v) → v = 0) :
    N ⊓ r.action.asGroupHom.ker = ⊥ := by
  letI : N.Normal := hN.1
  by_contra hne
  have he := hN.2.2 (N ⊓ r.action.asGroupHom.ker) inferInstance hne inf_le_left
  have hNK : N ≤ r.action.asGroupHom.ker := by rw [← he]; exact inf_le_right
  letI : Nontrivial r.Space := (irreducibleEnvelope r).nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : r.Space)
  apply hv
  apply hfix
  intro n
  have ha : r.action n.1 = 1 := congrArg Units.val (MonoidHom.mem_ker.mp (hNK n.2))
  rw [ha, Module.End.one_apply]

private theorem finset_sup_centerless
    (S : Finset (Subgroup G))
    (hS : ∀ N ∈ S, IsMinimalNormalSubgroup N ∧ ¬ IsMulCommutative N) :
    IsCenterless ↥(S.sup id) := by
  have he : minimalNormalSoclePart G (fun N => N ∈ S ∧ ¬ IsMulCommutative N) =
      S.sup id := by
    apply le_antisymm
    · apply minimalNormalSoclePart_le_of
      intro N _ hN
      exact Finset.le_sup (f := fun K : Subgroup G => K) hN.1
    · apply Finset.sup_le
      intro N hN
      exact minimalNormal_le_minimalNormalSoclePart _ N (hS N hN).1
        ⟨hN, (hS N hN).2⟩
  rw [← he]
  exact nonabelianMinimalNormalSoclePart_centerless G (fun N => N ∈ S)

private theorem kernel_inf_sup_eq_bot
    (r : FiniteIrreducibleRepresentation ℂ G)
    (S : Finset (Subgroup G))
    (hS : ∀ N ∈ S, IsMinimalNormalSubgroup N ∧ ¬ IsMulCommutative N)
    (hfix : ∀ N ∈ S, ∀ v : r.Space, (∀ n : N, r.action n.1 v = v) → v = 0) :
    S.sup id ⊓ r.action.asGroupHom.ker = ⊥ := by
  let K := r.action.asGroupHom.ker
  have hcentral : S.sup id ≤ Subgroup.centralizer (K : Set G) := by
    apply Finset.sup_le
    intro N hN
    letI : N.Normal := (hS N hN).1.1
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    apply le_antisymm ?_ bot_le
    exact (Subgroup.commutator_le_inf (H₁ := N) (H₂ := K)).trans_eq
      (minimal_kernel_inf_eq_bot r N (hS N hN).1 (hfix N hN))
  apply le_antisymm ?_ bot_le
  intro x hx
  have he : (⟨x, hx.1⟩ : ↥(S.sup id)) = 1 :=
    finset_sup_centerless S hS ⟨x, hx.1⟩ (by
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hcentral y.2) x hx.2)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)

omit [Finite G] in
private theorem finset_sup_normal (S : Finset (Subgroup G))
    (hS : ∀ N ∈ S, N.Normal) : (S.sup id : Subgroup G).Normal := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert N S _ ih =>
      letI : N.Normal := hS N (Finset.mem_insert_self _ _)
      letI : (S.sup id : Subgroup G).Normal := ih (fun M hM => hS M (Finset.mem_insert_of_mem hM))
      simpa only [Finset.sup_insert, id_eq] using
        (inferInstance : (N ⊔ S.sup id : Subgroup G).Normal)

/-- A finite actual family of nonabelian minimal normals shares one
irreducible detector. -/
theorem exists_for_finset
    (S : Finset (Subgroup G))
    (hS : ∀ N ∈ S, IsMinimalNormalSubgroup N ∧ ¬ IsMulCommutative N) :
    ∃ r : FiniteIrreducibleRepresentation ℂ G,
      ∀ N ∈ S, ∀ v : r.Space, (∀ n : N, r.action n.1 v = v) → v = 0 := by
  induction S using Finset.induction_on with
  | empty =>
      let E : Envelope G := {
        Space := ℂ
        addCommGroup := inferInstance
        module := inferInstance
        finiteDimensional := inferInstance
        nontrivial := inferInstance
        action := Representation.trivial ℂ G ℂ }
      obtain ⟨r, _, _⟩ := exists_irreducible_injection E
      exact ⟨r, by simp⟩
  | @insert M S _ ih =>
      have hM := hS M (Finset.mem_insert_self _ _)
      have hrest : ∀ N ∈ S, IsMinimalNormalSubgroup N ∧ ¬ IsMulCommutative N :=
        fun N hN => hS N (Finset.mem_insert_of_mem hN)
      obtain ⟨r, hr⟩ := ih hrest
      letI : M.Normal := hM.1.1
      rcases ZmudNormalDetection.irreducible_dichotomy r.action M with htriv | hfree
      · let B : Subgroup G := S.sup id
        letI : B.Normal := finset_sup_normal S (fun N hN => (hrest N hN).1.1)
        have hBK : B ⊓ r.action.asGroupHom.ker = ⊥ := kernel_inf_sup_eq_bot r S hrest hr
        have hMK : M ≤ r.action.asGroupHom.ker := by
          intro m hm
          apply MonoidHom.mem_ker.mpr
          apply Units.ext
          apply LinearMap.ext
          intro v
          exact htriv ⟨m, hm⟩ v
        have hnot : ¬ M ≤ B := by
          intro hMB
          apply hM.1.2.1
          apply le_antisymm ?_ bot_le
          intro m hm
          have hk : m ∈ B ⊓ r.action.asGroupHom.ker := ⟨hMB hm, hMK hm⟩
          rw [hBK] at hk
          exact hk
        let q := QuotientGroup.mk' B
        let N := M.map q
        letI : N.Normal := hM.1.1.map q (QuotientGroup.mk'_surjective B)
        have hN : N ≠ ⊥ := by
          intro hb
          apply hnot
          have hker := (Subgroup.map_eq_bot_iff (H := M)).mp hb
          simpa only [q, QuotientGroup.ker_mk'] using hker
        obtain ⟨F, hF⟩ := ZmudNormalDetection.exists_envelope N hN
        let F' := inflate q F
        have hFB : ∀ b : B, ∀ v : F'.Space, F'.action b.1 v = v := by
          intro b v
          change F.action (q b.1) v = v
          have hbq : q b.1 = 1 :=
            (QuotientGroup.eq_one_iff (N := B) (b.1 : G)).mpr b.2
          rw [hbq, map_one, Module.End.one_apply]
        have hFM : ∀ v : F'.Space, (∀ m : M, F'.action m.1 v = v) → v = 0 := by
          intro v hv
          apply hF
          intro n
          obtain ⟨m, hm, he⟩ := n.2
          have hmfix := hv ⟨m, hm⟩
          change F.action (q m) v = v at hmfix
          simpa only [he] using hmfix
        let E := ZmudTensorFixedSpaces.tensor (irreducibleEnvelope r) F'
        obtain ⟨s, j, hj⟩ := exists_irreducible_injection E
        refine ⟨s, ?_⟩
        intro K hK
        apply fixedFree_of_injection s E j hj K
        rcases Finset.mem_insert.mp hK with rfl | hKS
        · exact ZmudTensorFixedSpaces.fixedFree_right r.action F'.action K htriv hFM
        · apply ZmudTensorFixedSpaces.fixedFree_left r.action F'.action K (hr K hKS)
          intro k v
          exact hFB ⟨k.1, Finset.le_sup (f := id) hKS k.2⟩ v
      · refine ⟨r, ?_⟩
        intro N hN
        rcases Finset.mem_insert.mp hN with rfl | hNS
        · exact hfree
        · exact hr N hNS

/-- One detector covers every nonabelian actual minimal normal subgroup. -/
theorem exists_irreducible :
    ∃ r : FiniteIrreducibleRepresentation ℂ G,
      ∀ (N : Subgroup G), IsMinimalNormalSubgroup N → ¬ IsMulCommutative N →
        ∀ v : r.Space, (∀ n : N, r.action n.1 v = v) → v = 0 := by
  let S : Finset (Subgroup G) := Finset.univ.filter
    (fun N => IsMinimalNormalSubgroup N ∧ ¬ IsMulCommutative N)
  obtain ⟨r, hr⟩ := exists_for_finset S (by
    intro N hN
    exact (Finset.mem_filter.mp hN).2)
  exact ⟨r, fun N hN hn => hr N (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN, hn⟩)⟩

end SymmetricSubgroupAsymptotics.ZmudNonabelianSocleDetection
