import SymmetricSubgroupAsymptotics.CFSGHermitianIndependentMixedRatios

/-! One mixed scalar works across an opposed pair of singular planes.
Independent directions are compared by a constructed isotropic rectangle;
collinear directions are connected through a vector outside their line.
This proves the polar-rank-two case without a common-kernel hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem hermitian_rankTwo_opposed_common_ratio
    (eps : K) (heps : eps ≠ 0)
    (hflip : ∀ v w, hermitianPair sigma H v w = eps * sigma (hermitianPair sigma H w v))
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hdP : Module.finrank K P.val = 2)
    (hdZ : Module.finrank K Z.val = 2) (hdis : Disjoint P.val Z.val)
    (hNDp : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hNDz : ∀ y ∈ Z.val, (∀ x ∈ P.val, hermitianPair sigma H y x = 0) → y = 0)
    (hlinear : ∀ M : MaximalSpace sigma H,
      Nonempty (SemilinearPiece sigma H f ⟨M.val, M.property.1⟩ (RingEquiv.refl K)))
    (hfixP : ∀ R : SingularPoint sigma H, R.val ≤ P.val → f R = R)
    (hfixZ : ∀ R : SingularPoint sigma H, R.val ≤ Z.val → f R = R) :
    ∃ t : K, t ≠ 0 ∧ ∀ (x y : I → K), x ∈ P.val → x ≠ 0 → y ∈ Z.val → y ≠ 0 →
      hermitianPair sigma H y x = 0 → ∀ (hxy0 : x + y ≠ 0)
        (hz : hermitianPair sigma H (x + y) (x + y) = 0),
      (f (singularRay sigma H (x + y) hxy0 hz)).val = K ∙ (x + t • y) := by
  classical
  let Y := {y : Z.val // y ≠ 0}
  have hY (y : Y) : y.val.val ≠ 0 := fun h => y.property (Subtype.ext h)
  have hnotP (y : Y) : y.val.val ∉ P.val := by
    intro hp
    exact hY y ((Submodule.disjoint_def.mp hdis) y.val.val hp y.val.property)
  have hright (y : Y) := exists_hermitian_mixed_ray_ratio_of_two_le sigma H hswap f P
    (by omega : 2 ≤ Module.finrank K P.val) hlinear y.val.val
    (Z.property _ y.val.property _ y.val.property) (hnotP y) hfixP
    (fun R hR => hfixZ R (hR.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr y.val.property)))
  choose t ht htr using hright
  have heq_independent (a b : Y) (hab : LinearIndependent K ![a.val.val,b.val.val]) : t a = t b := by
    have hle : Submodule.span K (Set.range ![a.val.val,b.val.val]) ≤ Z.val := by
      apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      fin_cases j
      · exact a.val.property
      · exact b.val.property
    have hdspan : Module.finrank K (Submodule.span K (Set.range ![a.val.val,b.val.val])) = 2 := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hab
    have hspan : Submodule.span K (Set.range ![a.val.val,b.val.val]) = Z.val :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [hdZ, hdspan])
    exact hermitian_mixed_ratios_eq_of_independent sigma H eps heps hflip hswap f hf P Z
      hdis hdP hNDp hNDz hlinear hfixP hfixZ ![a.val.val,b.val.val] hspan hab
      (t a) (t b) (htr a) (htr b)
  have hconstant (a b : Y) : t a = t b := by
    by_cases hba : b.val.val ∈ K ∙ a.val.val
    · have hnot : ¬ Z.val ≤ K ∙ a.val.val := by
        intro hle
        have hh := Submodule.finrank_mono hle
        rw [hdZ, finrank_span_singleton (hY a)] at hh
        omega
      obtain ⟨z, hz, hznot⟩ := Set.not_subset.mp hnot
      have hz0 : z ≠ 0 := fun h => hznot (h ▸ (K ∙ a.val.val).zero_mem)
      let c : Y := ⟨⟨z, hz⟩, fun h => hz0 (congrArg Subtype.val h)⟩
      have hac : LinearIndependent K ![a.val.val,c.val.val] := by
        apply (LinearIndependent.pair_iff' (hY a)).mpr
        intro d he
        apply hznot
        have he' : d • a.val.val = z := he
        rw [← he']
        exact (K ∙ a.val.val).smul_mem d (Submodule.mem_span_singleton_self _)
      have hbc : LinearIndependent K ![b.val.val,c.val.val] := by
        apply (LinearIndependent.pair_iff' (hY b)).mpr
        intro d he
        apply hznot
        have he' : d • b.val.val = z := he
        rw [← he']
        exact (K ∙ a.val.val).smul_mem d hba
      exact (heq_independent a c hac).trans (heq_independent b c hbc).symm
    · have hab : LinearIndependent K ![a.val.val,b.val.val] :=
        (LinearIndependent.pair_iff' (hY a)).mpr (fun c he =>
          hba (he ▸ (K ∙ a.val.val).smul_mem c (Submodule.mem_span_singleton_self _)))
      exact heq_independent a b hab
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Z.val)
    (Submodule.one_le_finrank_iff.mp (by omega : 1 ≤ Module.finrank K Z.val))
  let y₀ : Y := ⟨⟨y, hy⟩, fun h => hy0 (congrArg Subtype.val h)⟩
  refine ⟨t y₀, ht y₀, ?_⟩
  intro x y hx _ hy hy0 hxy hsum0 hsum
  let y' : Y := ⟨⟨y, hy⟩, fun h => hy0 (congrArg Subtype.val h)⟩
  have he := htr y' x ⟨hx, hxy⟩ hsum0 hsum
  rw [hconstant y' y₀] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
