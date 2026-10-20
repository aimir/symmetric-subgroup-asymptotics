import SymmetricSubgroupAsymptotics.SolubleSubdirectSocleHeight

/-! The literal upper socle height does not increase on an actual normal
subgroup of a finite soluble group. Socles are retained as actual normal
subgroups; there is no choice of an unrelated semisimple series. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
open SolubleSocleConjugationModule

variable {G : Type} [Group G] [Finite G]

/-- The socle of an actual normal subgroup is normal in the original
ambient group, by invariance under the actual conjugation automorphisms. -/
instance normalSubgroupSocle_normal (N : Subgroup G) [N.Normal] :
    ((finiteGroupSocle N).map N.subtype).Normal := by
  constructor
  rintro _ ⟨n, hn, rfl⟩ g
  refine ⟨MulAut.conjNormal g n, ?_, rfl⟩
  exact SocleSurjectiveImage.socle_le_comap
    (MulAut.conjNormal (H := N) g).toMonoidHom
    (MulAut.conjNormal (H := N) g).surjective hn

private theorem minimalNormal_le_normalSubgroupSocle
    (N E : Subgroup G) [N.Normal] (hE : IsMinimalNormalSubgroup E)
    (hEN : E ≤ N) : E ≤ (finiteGroupSocle N).map N.subtype := by
  letI : E.Normal := hE.1
  have he : E.subgroupOf N ≠ ⊥ := by
    intro hz
    have h := congrArg (Subgroup.map N.subtype) hz
    rw [Subgroup.map_subgroupOf_eq_of_le hEN, Subgroup.map_bot] at h
    exact hE.2.1 h
  let good : Subgroup N → Prop := fun M => M.Normal ∧ M ≠ ⊥
  obtain ⟨M, hME, hM⟩ := Finite.exists_le_minimal (p := good)
    (a := E.subgroupOf N) ⟨inferInstance, he⟩
  have hmin : IsMinimalNormalSubgroup M := by
    refine ⟨hM.1.1, hM.1.2, ?_⟩
    intro K hK hn hKM
    exact hM.eq_of_le ⟨hK, hn⟩ hKM
  let S : Subgroup G := (finiteGroupSocle N).map N.subtype
  have hMS : M.map N.subtype ≤ S := by
    apply Subgroup.map_mono
    intro m hm
    exact Subgroup.subset_normalClosure ⟨M, hmin, hm⟩
  have hM0 : M.map N.subtype ≠ ⊥ := by
    intro hbot
    apply hM.1.2
    exact (Subgroup.map_eq_bot_iff_of_injective M Subtype.val_injective).mp hbot
  have hMinE : M.map N.subtype ≤ E := by
    calc
      M.map N.subtype ≤ (E.subgroupOf N).map N.subtype := Subgroup.map_mono hME
      _ = E := Subgroup.map_subgroupOf_eq_of_le hEN
  have hcap : E ⊓ S ≠ ⊥ := by
    intro hbot
    exact hM0 (bot_unique ((le_inf hMinE hMS).trans_eq hbot))
  have hEq : E ⊓ S = E := hE.2.2 (E ⊓ S) inferInstance hcap inf_le_left
  rw [← hEq]
  exact inf_le_right

/-- A normal subgroup's intersection with the original soluble socle lies
in its own literal socle. The submodule argument retains all primes. -/
theorem socle_intersection_le_normalSubgroupSocle [IsSolvable G]
    (N : Subgroup G) [N.Normal] :
    (finiteGroupSocle G).subgroupOf N ≤ finiteGroupSocle N := by
  let S := finiteGroupSocle G
  letI : IsMulCommutative S := socle_isMulCommutative (G := G)
  letI : IsSemisimpleModule ℤ[G] (representation S).asModule :=
    socle_isSemisimple (G := G)
  let V := normalSubmodule S N
  let T := (finiteGroupSocle N).map N.subtype
  have hVT : V ≤ normalSubmodule S T := by
    rw [← IsSemisimpleModule.sSup_simples_le V]
    apply sSup_le
    rintro W ⟨hW, hWV⟩ v hv
    have hmin := simple_isMinimalNormal S W hW
    have hEN : submoduleGroup S W ≤ N := by
      rintro _ ⟨s, hs, rfl⟩
      exact hWV hs
    exact minimalNormal_le_normalSubgroupSocle N _ hmin hEN
      ((mem_submoduleGroup S W v.toMul).mpr hv)
  intro n hn
  have hv : (Additive.ofMul (⟨(n : G), hn⟩ : S) : (representation S).asModule) ∈ V :=
    n.property
  obtain ⟨m, hm, he⟩ := hVT hv
  have hmn : m = n := Subtype.ext he
  simpa only [hmn] using hm

/-- Normal subgroups of finite soluble groups have no greater literal
upper socle height. -/
theorem height_normal {n : ℕ} [IsSolvable G]
    (N : Subgroup G) [N.Normal] (h : Height n G) : Height n N := by
  induction n generalizing G with
  | zero =>
    letI : Subsingleton G := h
    exact (inferInstance : Subsingleton N)
  | succ n ih =>
    let q := QuotientGroup.mk' (finiteGroupSocle G)
    let f : N →* (G ⧸ finiteGroupSocle G) := q.comp N.subtype
    have hr : f.range = N.map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    letI : f.range.Normal := by
      rw [hr]
      exact Subgroup.Normal.map inferInstance q
        (QuotientGroup.mk'_surjective (finiteGroupSocle G))
    have hh : Height n f.range := ih f.range h
    have hk : f.ker ≤ finiteGroupSocle N := by
      intro z hz
      apply socle_intersection_le_normalSubgroupSocle N
      have hz' : q (z : G) = 1 := hz
      exact (QuotientGroup.eq_one_iff (z : G)).mp hz'
    apply height_succ_of_quotient f.ker hk
    exact (height_equiv (QuotientGroup.quotientKerEquivRange f)).mpr hh

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
