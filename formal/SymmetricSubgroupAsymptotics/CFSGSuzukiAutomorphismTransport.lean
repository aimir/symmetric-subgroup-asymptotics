import SymmetricSubgroupAsymptotics.CFSGSuzukiQuotientStep

/-! Automorphism and subtype transport for Suzuki's normalizer induction.
The characteristic subgroup, its chosen intravariant subgroup and the
normalizer remain literal subgroups of the original ambient group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def restrictedAutomorphism {G : Type*} [Group G] (a : MulAut G)
    (K : Subgroup G) (hK : K.map a.toMonoidHom = K) : MulAut K :=
  (a.subgroupMap K).trans (MulEquiv.subgroupCongr hK)

theorem map_restrictedAutomorphism_subtype {G : Type*} [Group G]
    (a : MulAut G) (K : Subgroup G) (hK : K.map a.toMonoidHom = K)
    (H : Subgroup K) :
    (H.map (restrictedAutomorphism a K hK).toMonoidHom).map K.subtype =
      (H.map K.subtype).map a.toMonoidHom := by
  have hf : K.subtype.comp (restrictedAutomorphism a K hK).toMonoidHom =
      a.toMonoidHom.comp K.subtype := by ext x; rfl
  rw [Subgroup.map_map, Subgroup.map_map, hf]

theorem map_conj_subtype {G : Type*} [Group G]
    (K : Subgroup G) (H : Subgroup K) (g : K) :
    (H.map (MulAut.conj g).toMonoidHom).map K.subtype =
      (H.map K.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  have hf : K.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := by ext x; rfl
  rw [Subgroup.map_map, Subgroup.map_map, hf]

theorem map_automorphism_symm_cancel {G : Type*} [Group G]
    (H : Subgroup G) (a : MulAut G) :
    (H.map a.toMonoidHom).map a.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : a.symm.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
    ext x
    exact a.symm_apply_apply x
  rw [he, Subgroup.map_id]

theorem characteristic_subgroup_intravariant_class {G : Type*} [Group G]
    (E : Subgroup G) [E.Characteristic] (H : Subgroup E) (hH : Intravariant H)
    (a : MulAut G) :
    ∃ u : E, (H.map E.subtype).map a.toMonoidHom =
      (H.map E.subtype).map (MulAut.conj (u : G)).toMonoidHom := by
  have hEa : E.map a.toMonoidHom = E := Subgroup.characteristic_iff_map_eq.mp inferInstance a
  obtain ⟨u, hu⟩ := hH (restrictedAutomorphism a E hEa)
  refine ⟨u, ?_⟩
  have h := congrArg (fun L : Subgroup E => L.map E.subtype) hu
  change (H.map (restrictedAutomorphism a E hEa).toMonoidHom).map E.subtype =
    (H.map (MulAut.conj u).toMonoidHom).map E.subtype at h
  rw [map_restrictedAutomorphism_subtype, map_conj_subtype] at h
  exact h

theorem intravariant_normalizer_step {G : Type*} [Group G]
    (E : Subgroup G) [E.Characteristic] (H : Subgroup E) (hH : Intravariant H)
    (S : Subgroup (Subgroup.normalizer (H.map E.subtype : Set G)))
    (hS : Intravariant S) :
    Intravariant (S.map (Subgroup.normalizer (H.map E.subtype : Set G)).subtype) := by
  let P := H.map E.subtype
  let N := Subgroup.normalizer (P : Set G)
  intro a
  obtain ⟨u, hu⟩ := characteristic_subgroup_intravariant_class E H hH a
  let c : MulAut G := MulAut.conj (u : G)
  let b : MulAut G := a.trans c.symm
  have hPa : P.map a.toMonoidHom = P.map c.toMonoidHom := hu
  have hPb : P.map b.toMonoidHom = P := by
    calc
      _ = (P.map a.toMonoidHom).map c.symm.toMonoidHom := by
        have hf : b.toMonoidHom = c.symm.toMonoidHom.comp a.toMonoidHom := by ext x; rfl
        exact (congrArg (fun f : G →* G => P.map f) hf).trans
          (Subgroup.map_map P c.symm.toMonoidHom a.toMonoidHom).symm
      _ = (P.map c.toMonoidHom).map c.symm.toMonoidHom := by rw [hPa]
      _ = P := map_automorphism_symm_cancel P c
  have hNb : N.map b.toMonoidHom = N := by
    calc
      _ = Subgroup.normalizer ((P.map b.toMonoidHom) : Set G) :=
        Subgroup.map_equiv_normalizer_eq P b
      _ = N := by rw [hPb]
  obtain ⟨v, hv⟩ := hS (restrictedAutomorphism b N hNb)
  have hvG : (S.map N.subtype).map b.toMonoidHom =
      (S.map N.subtype).map (MulAut.conj (v : G)).toMonoidHom := by
    have h := congrArg (fun L : Subgroup N => L.map N.subtype) hv
    change (S.map (restrictedAutomorphism b N hNb).toMonoidHom).map N.subtype =
      (S.map (MulAut.conj v).toMonoidHom).map N.subtype at h
    rw [map_restrictedAutomorphism_subtype, map_conj_subtype] at h
    exact h
  refine ⟨(u : G) * v, ?_⟩
  have hleft : ((S.map N.subtype).map b.toMonoidHom).map c.toMonoidHom =
      (S.map N.subtype).map a.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    change c (c.symm (a x)) = a x
    exact c.apply_symm_apply _
  have hright : ((S.map N.subtype).map (MulAut.conj (v : G)).toMonoidHom).map c.toMonoidHom =
      (S.map N.subtype).map (MulAut.conj ((u : G) * v)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    change (u : G) * ((v : G) * x * (v : G)⁻¹) * (u : G)⁻¹ =
      ((u : G) * v) * x * ((u : G) * v)⁻¹
    group
  have h := congrArg (fun L : Subgroup G => L.map c.toMonoidHom) hvG
  change ((S.map N.subtype).map b.toMonoidHom).map c.toMonoidHom =
    ((S.map N.subtype).map (MulAut.conj (v : G)).toMonoidHom).map c.toMonoidHom at h
  rw [hleft, hright] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReduction
