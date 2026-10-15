import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Two actual normal axes can share one socle generator when an ambient
normal subgroup separates their actions. An image normal cover lifts to
an intrinsic normal-axis dichotomy without any direct-product assumption.
Every quotient is then controlled by one of two displayed quotient maps,
or by the socle of the original group when its kernel is trivial. -/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.SeparatedNormalAxesQuotientSocles

variable {G : Type} [Group G]

/-- An actual image normal cover lifts through a kernel centralized by
an ambient normal subgroup acting fully on the proposed core. -/
theorem normal_contains_or_le_kernel
    {Q : Type} [Group Q] (q : G →* Q) (hq : Function.Surjective q)
    (D A : Subgroup G) [D.Normal] [A.Normal]
    (hfull : ⁅D,A⁆ = A)
    (hcentral : q.ker ≤ Subgroup.centralizer (D : Set G))
    (hcover : ∀ M : Subgroup Q, M.Normal → M ≠ ⊥ → A.map q ≤ M)
    (N : Subgroup G) (hN : N.Normal) : A ≤ N ∨ N ≤ q.ker := by
  letI := hN
  by_cases hb : N.map q = ⊥
  · exact Or.inr ((Subgroup.map_eq_bot_iff (H := N)).mp hb)
  · left
    have himage : A.map q ≤ N.map q := hcover _ (hN.map q hq) hb
    have hjoin : A ≤ N ⊔ q.ker := by
      intro a ha
      obtain ⟨n,hn,he⟩ := himage (show q a ∈ A.map q from ⟨a,ha,rfl⟩)
      have hd : n⁻¹*a ∈ q.ker := by
        rw [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
      have hm := (N ⊔ q.ker).mul_mem (Subgroup.mem_sup_left hn)
        (Subgroup.mem_sup_right hd)
      simpa only [mul_inv_cancel_left] using hm
    let pi : G →* G ⧸ N := QuotientGroup.mk' N
    have hDB : ⁅D,q.ker⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
    have hmapN : N.map pi = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := N)).mpr
      simpa only [pi,QuotientGroup.ker_mk'] using (le_refl N)
    have hmapJoin : (N ⊔ q.ker).map pi = q.ker.map pi := by
      rw [Subgroup.map_sup,hmapN,bot_sup_eq]
    have hcommJoin : ⁅D,N ⊔ q.ker⁆ ≤ N := by
      have hmap : (⁅D,N ⊔ q.ker⁆).map pi = ⊥ := by
        rw [Subgroup.map_commutator,hmapJoin,← Subgroup.map_commutator,
          hDB,Subgroup.map_bot]
      have hle := (Subgroup.map_eq_bot_iff (H := ⁅D,N ⊔ q.ker⁆)).mp hmap
      simpa only [pi,QuotientGroup.ker_mk'] using hle
    rw [← hfull]
    exact (Subgroup.commutator_mono le_rfl hjoin).trans hcommJoin

theorem socle_eq_sup
    (A B : Subgroup G) (hA : IsMinimalNormalSubgroup A)
    (hB : IsMinimalNormalSubgroup B)
    (haxes : ∀ N : Subgroup G, N.Normal → A ≤ N ∨ N ≤ B) :
    finiteGroupSocle G = A ⊔ B := by
  letI := hA.1
  letI := hB.1
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨N,hN,hx⟩
    rcases haxes N hN.1 with ha | hb
    · have he : A = N := hN.2.2 A hA.1 hA.2.1 ha
      exact Subgroup.mem_sup_left (he.symm ▸ hx)
    · exact Subgroup.mem_sup_right (hb hx)
  · apply sup_le
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨A,hA,hx⟩
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨B,hB,hx⟩

theorem normalGen_le_one_of_minimal
    (A : Subgroup G) (hA : IsMinimalNormalSubgroup A) :
    MarkedC4.normalGen A ≤ 1 := by
  letI := hA.1
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hA.2.1
  let T := Subgroup.normalClosure (Set.range (fun _ : Fin 1 => a))
  have hTA : T ≤ A := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,rfl⟩
    exact ha
  have hTne : T ≠ ⊥ := by
    intro h
    apply hane
    have hm : a ∈ T := Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
    rw [h] at hm
    exact Subgroup.mem_bot.mp hm
  exact normalGen_le_of_fin_tuple (fun _ : Fin 1 => a)
    (hA.2.2 T inferInstance hTne hTA)

theorem socle_one [Finite G]
    (A B : Subgroup G) (hA : IsMinimalNormalSubgroup A)
    (hB : IsMinimalNormalSubgroup B)
    (haxes : ∀ N : Subgroup G, N.Normal → A ≤ N ∨ N ≤ B)
    (hsep : NoCommonNormalQuotient A B) : SocleNormalGeneratorBound G 1 := by
  letI := hA.1
  letI := hB.1
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr
  rw [socle_eq_sup A B hA hB haxes]
  exact (normalGen_sup_le_max_of_noCommonNormalQuotient A B hsep).trans
    (max_le (normalGen_le_one_of_minimal A hA) (normalGen_le_one_of_minimal B hB))

/-- Both smaller groups are targets of specified maps from the original
group. The proof factors each original quotient through one of those maps;
it never replaces an original kernel by an abstract isomorphic subgroup. -/
theorem socle_of_surjective [Finite G]
    {P Q : Type} [Group P] [Group Q]
    (p : G →* P) (hp : Function.Surjective p)
    (q : G →* Q) (hq : Function.Surjective q)
    (hA : IsMinimalNormalSubgroup p.ker) (hB : IsMinimalNormalSubgroup q.ker)
    (haxes : ∀ N : Subgroup G, N.Normal → p.ker ≤ N ∨ N ≤ q.ker)
    (hsep : NoCommonNormalQuotient p.ker q.ker)
    {t : ℕ} (ht : 1 ≤ t)
    (hP : ∀ N : Subgroup P, ∀ _ : N.Normal, SocleNormalGeneratorBound (P ⧸ N) t)
    (hQ : ∀ N : Subgroup Q, ∀ _ : N.Normal, SocleNormalGeneratorBound (Q ⧸ N) t)
    {X : Type} [Group X] (rho : G →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X t := by
  rcases haxes rho.ker inferInstance with ha | hb
  · obtain ⟨f,hf,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor p hp rho hrho ha
    exact CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.quotientKerEquivOfSurjective f hf) (hP f.ker inferInstance)
  · by_cases htrivial : rho.ker = ⊥
    · exact CyclicSocleQuotientTools.socleBound_equiv
        (MulEquiv.ofBijective rho ⟨(MonoidHom.ker_eq_bot_iff rho).mp htrivial,hrho⟩)
        ((socle_one p.ker q.ker hA hB haxes hsep).mono ht)
    · have he : rho.ker = q.ker := hB.2.2 rho.ker inferInstance htrivial hb
      obtain ⟨f,hf,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor q hq rho hrho
        (le_of_eq he.symm)
      exact CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf) (hQ f.ker inferInstance)

end SymmetricSubgroupAsymptotics.SeparatedNormalAxesQuotientSocles

end
