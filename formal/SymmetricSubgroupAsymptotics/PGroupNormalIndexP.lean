import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-! Original ambient-normal index-p steps and their invariant-character
certificates. The p-group hypothesis makes a normal section of order p
central in the original quotient ambient group. Each such section is the
kernel of a nonzero character invariant under all original conjugations.
No monotonicity of subgroup generator rank is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A strict original normal interval has an original normal bottom step
of relative index p. -/
theorem pGroup_normal_interval_bottom_step (hG : IsPGroup p G)
    (H M : Subgroup G) [H.Normal] [M.Normal] (hHM : H < M) :
    ∃ J : Subgroup G, J.Normal ∧ H < J ∧ J ≤ M ∧ H.relIndex J = p := by
  obtain ⟨z,hzc,hzp,hHJ,hJM⟩ := pGroup_normal_interval_step hG H M hHM
  obtain ⟨hJ,hi⟩ := central_prime_preimage_properties H z hzc hzp
  exact ⟨_,hJ,hHJ,hJM,hi⟩

/-- A normal section of order p in a finite p-group is central in the
actual quotient of the whole original ambient group. -/
theorem pGroup_normal_index_p_central (hG : IsPGroup p G)
    (H M : Subgroup G) [H.Normal] [M.Normal]
    (hHM : H ≤ M) (hindex : H.relIndex M = p) :
    ∀ m : G, m ∈ M → QuotientGroup.mk' H m ∈ Subgroup.center (G ⧸ H) := by
  have hlt : H < M := lt_of_le_of_ne hHM (by
    intro he
    subst M
    exact (Fact.out : p.Prime).ne_one
      (by simpa only [Subgroup.relIndex_self] using hindex.symm))
  obtain ⟨z,hzc,hzp,hHK,hKM⟩ := pGroup_normal_interval_step hG H M hlt
  let K := (Subgroup.zpowers z).comap (QuotientGroup.mk' H)
  have hHKindex : H.relIndex K = p :=
    (central_prime_preimage_properties H z hzc hzp).2
  have hprod := Subgroup.relIndex_mul_relIndex H K M hHK.le hKM
  rw [hHKindex,hindex] at hprod
  have hKMindex : K.relIndex M = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos
    simpa only [Nat.mul_one] using hprod
  have he : K = M := le_antisymm hKM (Subgroup.relIndex_eq_one.mp hKMindex)
  intro m hm
  have hmK : m ∈ K := he.symm ▸ hm
  exact Subgroup.zpowers_le.mpr hzc hmK

/-- Every strict original normal interval also has an original normal
top step of index p. This is a finite normal-poset argument, not a claim
that arbitrary subgroups normal in M are normal in G. -/
theorem pGroup_normal_interval_top_step (hG : IsPGroup p G)
    (H M : Subgroup G) [H.Normal] [M.Normal] (hHM : H < M) :
    ∃ J : Subgroup G, J.Normal ∧ H ≤ J ∧ J < M ∧ J.relIndex M = p := by
  classical
  let S : Set (Subgroup G) := {J | J.Normal ∧ H ≤ J ∧ J < M}
  obtain ⟨J,hHJ,hmax⟩ := (Set.toFinite S).exists_le_maximal
    (show H ∈ S from ⟨inferInstance,le_rfl,hHM⟩)
  letI : J.Normal := hmax.1.1
  obtain ⟨K,hK,hJK,hKM,hindex⟩ :=
    pGroup_normal_interval_bottom_step hG J M hmax.1.2.2
  have he : K = M := by
    by_contra hne
    have hKS : K ∈ S := ⟨hK,hmax.1.2.1.trans hJK.le,lt_of_le_of_ne hKM hne⟩
    exact hJK.not_ge (hmax.2 hKS hJK.le)
  exact ⟨J,inferInstance,hHJ,hmax.1.2.2,he ▸ hindex⟩

/-- Every original ambient-normal subgroup of index p in M is the
literal mapped kernel of a nonzero whole-ambient invariant character. -/
theorem pGroup_normal_index_p_character (hG : IsPGroup p G)
    (H M : Subgroup G) [H.Normal] [M.Normal]
    (hHM : H ≤ M) (hindex : H.relIndex M = p) :
    ∃ χ : primeRelativeCharacters p M, χ ≠ 0 ∧
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map M.subtype = H := by
  let D := H.subgroupOf M
  have hcard : Nat.card (M ⧸ D) = p := hindex
  let e : M ⧸ D ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (by simp)
  let q := QuotientGroup.mk' D
  let f : M →* Multiplicative (ZMod p) := e.toMonoidHom.comp q
  let χ : PrimeCharacters p M := AddMonoidHom.toMultiplicativeRight.symm f
  have hχ : χ ∈ primeRelativeCharacters p M := by
    intro g m
    change f (⟨g*(m:G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ m.2 g⟩ : M) = f m
    apply congrArg e
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (g*(m:G)*g⁻¹) / (m:G) ∈ H
    have hc := pGroup_normal_index_p_central hG H M hHM hindex (m:G) m.2
    have he : QuotientGroup.mk' H (g*(m:G)*g⁻¹) = QuotientGroup.mk' H (m:G) := by
      rw [map_mul,map_mul,map_inv,Subgroup.mem_center_iff.mp hc]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
    exact QuotientGroup.eq_iff_div_mem.mp he
  have hker : f.ker = D := by
    ext m
    change e (q m) = 1 ↔ m ∈ D
    rw [← map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff m
  have hnonzero : (⟨χ,hχ⟩ : primeRelativeCharacters p M) ≠ 0 := by
    intro hz
    have he : χ = 0 := congrArg Subtype.val hz
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective D)
    obtain ⟨m,hm⟩ := hf (Multiplicative.ofAdd (1 : ZMod p))
    have hmzero : f m = 1 := DFunLike.congr_fun he (Additive.ofMul m)
    have hbad : (1 : ZMod p) = 0 := hm.symm.trans hmzero
    exact one_ne_zero hbad
  refine ⟨⟨χ,hχ⟩,hnonzero,?_⟩
  change f.ker.map M.subtype = H
  rw [hker]
  exact Subgroup.map_subgroupOf_eq_of_le hHM

/-- The number of literal G-normal index-p subgroups of the original M
is at most the number of nonzero invariant characters. Scalar multiples
may have the same kernel; only this upper bound is needed. -/
theorem pGroup_normal_index_p_count_le (hG : IsPGroup p G)
    (M : Subgroup G) [M.Normal] :
    Nat.card {H : Subgroup G // H.Normal ∧ H ≤ M ∧ H.relIndex M = p} ≤
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p M) - 1 := by
  classical
  let A := {H : Subgroup G // H.Normal ∧ H ≤ M ∧ H.relIndex M = p}
  let V := primeRelativeCharacters p M
  have hex (H : A) : ∃ χ : V, χ ≠ 0 ∧
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map M.subtype = H.1 := by
    letI : H.1.Normal := H.2.1
    exact pGroup_normal_index_p_character hG H.1 M H.2.2.1 H.2.2.2
  let f : A → {χ : V // χ ≠ 0} :=
    fun H => ⟨(hex H).choose,(hex H).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro H K he
    have hc := congrArg Subtype.val he
    apply Subtype.ext
    exact (hex H).choose_spec.2.symm.trans
      ((congrArg (fun χ : V => (AddMonoidHom.toMultiplicativeRight χ.1).ker.map M.subtype)
        hc).trans (hex K).choose_spec.2)
  have hcard := Nat.card_le_card_of_injective f hf
  have hlt : Nat.card {χ : V // χ ≠ 0} < Nat.card V := by
    letI := Fintype.ofFinite V
    letI := Fintype.ofFinite {χ : V // χ ≠ 0}
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_lt (p := fun χ : V => χ ≠ 0) (x := 0) (by simp))
  have hV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  rw [hV] at hlt
  exact hcard.trans (Nat.le_sub_one_of_lt hlt)

end SymmetricSubgroupAsymptotics
