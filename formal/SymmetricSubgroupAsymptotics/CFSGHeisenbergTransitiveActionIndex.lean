import SymmetricSubgroupAsymptotics.AdditiveNonzeroOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-! A dimension-uniform SAME-subgroup Heisenberg index bound. The
actual Heisenberg kernel preimage and the actual Levi projection come
from one subgroup M. The vector image is only additive. A literal
transitive action on the nonzero vector quotient supplies the second
factor; the prime-field isotropy theorem supplies the first factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergTransitiveActionIndex

open CFSGHeisenbergCoordinateGroup CFSGHeisenbergFiniteFieldIsotropy
variable {K G : Type*} [Field K] [Group G] {m : ℕ}

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (ψ : B →* MulAut A) : Finite (A ⋊[ψ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

theorem vector_conjugate (k g : Element K m) :
    ((k * g * k⁻¹).a, (k * g * k⁻¹).b) = (g.a, g.b) := by
  have he : projection (k * g * k⁻¹) = projection g := by
    rw [map_mul, map_mul, map_inv]
    rw [mul_comm (projection k) (projection g), mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg Multiplicative.toAdd he

variable (φ : G →* MulAut (Element K m))

theorem conjugate_mem_preimage (M : Subgroup (Element K m ⋊[φ] G))
    (t : Element K m ⋊[φ] G) (ht : t ∈ M)
    (g : Element K m) (hg : g ∈ M.comap SemidirectProduct.inl) :
    t.left * φ t.right g * t.left⁻¹ ∈ M.comap SemidirectProduct.inl := by
  change SemidirectProduct.inl (t.left * φ t.right g * t.left⁻¹) ∈ M
  have he : (SemidirectProduct.inl (t.left * φ t.right g * t.left⁻¹) :
      Element K m ⋊[φ] G) = t * SemidirectProduct.inl g * t⁻¹ := by
    calc
      _ = SemidirectProduct.inl t.left *
          (SemidirectProduct.inr t.right * SemidirectProduct.inl g *
            SemidirectProduct.inr t.right⁻¹) * (SemidirectProduct.inl t.left)⁻¹ := by
        rw [map_mul, map_mul, map_inv, SemidirectProduct.inl_aut]
      _ = (SemidirectProduct.inl t.left * SemidirectProduct.inr t.right) *
          SemidirectProduct.inl g *
            (SemidirectProduct.inl t.left * SemidirectProduct.inr t.right)⁻¹ := by
        rw [map_inv]
        group
      _ = _ := by rw [SemidirectProduct.inl_left_mul_inr_right]
  rw [he]
  exact M.mul_mem (M.mul_mem ht hg) (M.inv_mem ht)

theorem subgroup_index_factor [Finite K] [Finite G]
    (M : Subgroup (Element K m ⋊[φ] G)) :
    M.index = (M.comap SemidirectProduct.inl).index *
      (M.map SemidirectProduct.rightHom).index := by
  have h := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    (SemidirectProduct.rightHom : Element K m ⋊[φ] G →* G)
    SemidirectProduct.rightHom_surjective M
  have hk : (M.comap SemidirectProduct.inl).index =
      M.relIndex (SemidirectProduct.rightHom : Element K m ⋊[φ] G →* G).ker := by
    rw [Subgroup.index_comap, SemidirectProduct.range_inl_eq_ker_rightHom]
  rw [← hk] at h
  exact h

variable [MulAction G ((Fin m → K) × (Fin m → K))]

theorem vectorImage_stable
    (hφ : ∀ A g, ((φ A g).a, (φ A g).b) = A • (g.a, g.b))
    (M : Subgroup (Element K m ⋊[φ] G))
    (A : G) (hA : A ∈ M.map SemidirectProduct.rightHom)
    (v : (Fin m → K) × (Fin m → K))
    (hv : v ∈ vectorImage (M.comap SemidirectProduct.inl)) :
    A • v ∈ vectorImage (M.comap SemidirectProduct.inl) := by
  let J := M.comap SemidirectProduct.inl
  change Multiplicative.ofAdd v ∈ J.map projection at hv
  obtain ⟨g, hg, hgv⟩ := hv
  have hgv' : (g.a, g.b) = v := congrArg Multiplicative.toAdd hgv
  obtain ⟨t, ht, htr⟩ := hA
  have htr' : t.right = A := htr
  let z := t.left * φ t.right g * t.left⁻¹
  have hz : z ∈ J := conjugate_mem_preimage φ M t ht g hg
  have he : (z.a, z.b) = A • v := by
    dsimp only [z]
    rw [vector_conjugate, hφ, htr', hgv']
  change Multiplicative.ofAdd (A • v) ∈ J.map projection
  refine ⟨z, hz, ?_⟩
  exact congrArg Multiplicative.ofAdd he

/-- The actual central-proper stabilizer has index at least p*q^(2m).
The abstract vector action hypotheses will be discharged by actual
symplectic matrix words; no full-field linearity of its image is used. -/
theorem prime_mul_field_power_le_index (p : ℕ) [Fact p.Prime] [CharP K p]
    [Finite K] [Finite G]
    (hzero : ∀ A : G, A • (0 : (Fin m → K) × (Fin m → K)) = 0)
    (htrans : ∀ v w : (Fin m → K) × (Fin m → K),
      v ≠ 0 → w ≠ 0 → ∃ A : G, A • v = w)
    (hφ : ∀ A g, ((φ A g).a, (φ A g).b) = A • (g.a, g.b))
    (M : Subgroup (Element K m ⋊[φ] G))
    (hcentre : ¬(central (K := K) (m := m)).range ≤ M.comap SemidirectProduct.inl) :
    p * Nat.card K ^ (2 * m) ≤ M.index := by
  let J := M.comap SemidirectProduct.inl
  let L := M.map SemidirectProduct.rightHom
  have hfactor : M.index = J.index * L.index := subgroup_index_factor φ M
  have hq : 0 < Nat.card K := Nat.card_pos
  by_cases hzeroJ : ∀ g ∈ J, (g.a, g.b) = 0
  · have hWbot : vectorImage J = ⊥ := by
      apply le_antisymm _ bot_le
      intro v hv
      change v = 0
      change Multiplicative.ofAdd v ∈ J.map projection at hv
      obtain ⟨g, hg, he⟩ := hv
      have he' : (g.a, g.b) = v := congrArg Multiplicative.toAdd he
      exact he'.symm.trans (hzeroJ g hg)
    have hcard : Nat.card J ≤ Nat.card (centralPreimage J) := by
      have hc := CFSGHeisenbergFiniteFieldIndex.subgroup_card_le_product J
      rw [hWbot, AddSubgroup.card_bot, mul_one] at hc
      exact hc
    have hsmall : p * Nat.card J ≤ Nat.card K :=
      (Nat.mul_le_mul_left p hcard).trans
        (proper_additive_card_mul_prime_le p _ (centralPreimage_ne_top J hcentre))
    have he := J.card_mul_index
    rw [CFSGHeisenbergCoordinateGroup.card] at he
    have hJ : p * Nat.card K ^ (2 * m) ≤ J.index := by
      apply Nat.le_of_mul_le_mul_left _ hq
      calc
        Nat.card K * (p * Nat.card K ^ (2 * m)) =
            p * Nat.card K ^ (2 * m + 1) := by rw [pow_succ]; ring
        _ = p * (Nat.card J * J.index) := congrArg (fun n : ℕ => p * n) he.symm
        _ = (p * Nat.card J) * J.index := (Nat.mul_assoc _ _ _).symm
        _ ≤ Nat.card K * J.index := Nat.mul_le_mul_right J.index hsmall
    rw [hfactor]
    exact hJ.trans (Nat.le_mul_of_pos_right _ (Nat.card_pos (α := G ⧸ L)))
  · have hex : ∃ g, g ∈ J ∧ (g.a, g.b) ≠ 0 := by
      simpa only [not_forall, exists_prop] using hzeroJ
    obtain ⟨g, hg, hne⟩ := hex
    have hmem : (g.a, g.b) ∈ vectorImage J := by
      change Multiplicative.ofAdd (g.a, g.b) ∈ J.map projection
      exact ⟨g, hg, rfl⟩
    have horbit := AdditiveNonzeroOrbitIndex.card_le_subgroup_card_mul_index
      hzero htrans L (vectorImage J) (vectorImage_stable φ hφ M) (g.a, g.b) hmem hne
    simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin] at horbit
    have hL : Nat.card K ^ m ≤ L.index := by
      apply Nat.le_of_mul_le_mul_left _ (pow_pos hq m)
      exact horbit.trans (Nat.mul_le_mul_right L.index (vectorImage_card_le p J hcentre))
    have hJ : p * Nat.card K ^ m ≤ J.index :=
      CFSGHeisenbergFiniteFieldIndex.index_least p J hcentre
    calc
      p * Nat.card K ^ (2 * m) = (p * Nat.card K ^ m) * Nat.card K ^ m := by
        rw [show 2 * m = m + m by omega, pow_add]
        ring
      _ ≤ J.index * L.index := Nat.mul_le_mul hJ hL
      _ = M.index := hfactor.symm

end SymmetricSubgroupAsymptotics.CFSGHeisenbergTransitiveActionIndex
