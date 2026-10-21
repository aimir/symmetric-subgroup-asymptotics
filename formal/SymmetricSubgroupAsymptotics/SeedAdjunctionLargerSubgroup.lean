import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionProperty

/-! A strict seed adjunction can be reduced to an already classified
larger seed by actual subgroup inclusion. This avoids a second join table
when every nontrivial root contains such a larger subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

def EqSeedOrContainsConjugate (H K W : Subgroup G) : Prop :=
  W = H ∨ ∃ c : G, MulAut.conj c • K ≤ W

theorem eqSeedOrContainsConjugate_conjugate (H K : Subgroup G)
    (c : G) (hc : MulAut.conj c • H = H) (W : Subgroup G)
    (hW : EqSeedOrContainsConjugate H K W) :
    EqSeedOrContainsConjugate H K (MulAut.conj c • W) := by
  rcases hW with rfl | ⟨d, hd⟩
  · exact Or.inl hc
  · right
    refine ⟨c * d, ?_⟩
    have hmap : MulAut.conj c • (MulAut.conj d • K) ≤ MulAut.conj c • W := by
      change (MulAut.conj d • K).map (MulAut.conj c).toMonoidHom ≤
        W.map (MulAut.conj c).toMonoidHom
      exact Subgroup.map_mono hd
    simpa only [map_mul, mul_smul] using hmap

theorem strict_adjoin_contains_of_forest {I : Type*} {generators : I → G}
    {H K : Subgroup G} {q r : ℕ}
    (C : FiniteLeftCosetCover generators H q)
    (D : FiniteNormalizerAdjunctionReduction H C.representatives r)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (hroot : ∀ k : Fin r, EqSeedOrContainsConjugate H K
      (H ⊔ Subgroup.closure {C.representatives (D.roots k)}))
    (g : G) (hg : g ∉ H) :
    ∃ c : G, MulAut.conj c • K ≤ H ⊔ Subgroup.closure {g} := by
  obtain ⟨i, hi⟩ := C.covers hgen g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (C.representatives i) hi
  have hp := D.property_representative (EqSeedOrContainsConjugate H K)
    (eqSeedOrContainsConjugate_conjugate H K) hroot i
  rw [← he] at hp
  rcases hp with heq | hcontains
  · have hmem : g ∈ H ⊔ Subgroup.closure {g} :=
      (show Subgroup.closure {g} ≤ H ⊔ Subgroup.closure {g} from le_sup_right)
        (Subgroup.subset_closure (by simp))
    exact False.elim (hg (heq ▸ hmem))
  · exact hcontains

namespace FiniteSubgroupAdjunctionCoverage

theorem complete_above_of_strict_contains {I : Type*} (rows : I → Subgroup G)
    (H K : Subgroup G) (hH : Covered rows H)
    (hK : ∀ W : Subgroup G, K ≤ W → Covered rows W)
    (hstrict : ∀ g : G, g ∉ H → ∃ c : G,
      MulAut.conj c • K ≤ H ⊔ Subgroup.closure {g})
    (U : Subgroup G) (hHU : H ≤ U) : Covered rows U := by
  classical
  by_cases heq : U = H
  · simpa only [heq] using hH
  · have hnot : ¬ U ≤ H := fun h => heq (le_antisymm h hHU)
    obtain ⟨g, hgU, hgH⟩ := Set.not_subset.mp hnot
    obtain ⟨c, hc⟩ := hstrict g hgH
    have hgenerated : H ⊔ Subgroup.closure {g} ≤ U :=
      sup_le hHU ((Subgroup.closure_le U).mpr (by
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact hgU))
    have hKU : MulAut.conj c • K ≤ U := hc.trans hgenerated
    have hmap : MulAut.conj c⁻¹ • (MulAut.conj c • K) ≤ MulAut.conj c⁻¹ • U := by
      change (MulAut.conj c • K).map (MulAut.conj c⁻¹).toMonoidHom ≤
        U.map (MulAut.conj c⁻¹).toMonoidHom
      exact Subgroup.map_mono hKU
    have hKW : K ≤ MulAut.conj c⁻¹ • U := by
      simpa only [map_inv, inv_smul_smul] using hmap
    have hcovered := covered_conjugate rows (hK _ hKW) c
    simpa only [map_inv, smul_inv_smul] using hcovered

end FiniteSubgroupAdjunctionCoverage
end SymmetricSubgroupAsymptotics

end
