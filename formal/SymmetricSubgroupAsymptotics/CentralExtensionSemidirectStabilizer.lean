import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-! A subgroup of a semidirect product with a nonabelian radical.
The projected subgroup preserves the intersection with a central layer
and the image in an abelian quotient. It need not preserve the radical
intersection itself. All three indices below belong to the same M. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CentralExtensionSemidirectStabilizer

variable {N T : Type*} [Group N] [Group T] (φ : T →* MulAut N)

theorem conjugate_inl (x : N ⋊[φ] T) (n : N) :
    x * SemidirectProduct.inl n * x⁻¹ =
      SemidirectProduct.inl (x.left * φ x.right n * x.left⁻¹) := by
  symm
  calc
    _ = SemidirectProduct.inl x.left *
        (SemidirectProduct.inr x.right * SemidirectProduct.inl n *
          SemidirectProduct.inr x.right⁻¹) * (SemidirectProduct.inl x.left)⁻¹ := by
      rw [map_mul, map_mul, map_inv, SemidirectProduct.inl_aut]
    _ = (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) *
        SemidirectProduct.inl n *
          (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right)⁻¹ := by
      rw [map_inv]
      group
    _ = _ := by rw [SemidirectProduct.inl_left_mul_inr_right]

theorem conjugate_mem_kernel (M : Subgroup (N ⋊[φ] T))
    (x : N ⋊[φ] T) (hx : x ∈ M) (n : N)
    (hn : n ∈ M.comap SemidirectProduct.inl) :
    x.left * φ x.right n * x.left⁻¹ ∈ M.comap SemidirectProduct.inl := by
  change SemidirectProduct.inl (x.left * φ x.right n * x.left⁻¹) ∈ M
  rw [← conjugate_inl φ x n]
  exact M.mul_mem (M.mul_mem hx hn) (M.inv_mem hx)

variable {V : Type*} [CommGroup V]

/-- Inner conjugation vanishes in the abelian quotient; it is not
discarded inside N. -/
theorem quotient_action_mem_of_projected (π : N →* V) (ψ : T →* MulAut V)
    (hπ : ∀ t n, π (φ t n) = ψ t (π n))
    (M : Subgroup (N ⋊[φ] T)) (t : T)
    (ht : t ∈ M.map SemidirectProduct.rightHom)
    (v : V) (hv : v ∈ (M.comap SemidirectProduct.inl).map π) :
    ψ t v ∈ (M.comap SemidirectProduct.inl).map π := by
  obtain ⟨x, hx, hr⟩ := ht
  change x.right = t at hr
  obtain ⟨n, hn, hnv⟩ := hv
  refine ⟨x.left * φ x.right n * x.left⁻¹,
    conjugate_mem_kernel φ M x hx n hn, ?_⟩
  rw [map_mul, map_mul, map_inv, hπ, hr, hnv]
  simp [mul_comm, mul_left_comm]

variable {Z : Type*} [Group Z]

/-- Centrality kills the inner correction on the central layer only. -/
theorem central_action_mem_of_projected (ι : Z →* N) (χ : T →* MulAut Z)
    (hι : ∀ t z, φ t (ι z) = ι (χ t z))
    (hcentral : ∀ z, ι z ∈ Subgroup.center N)
    (M : Subgroup (N ⋊[φ] T)) (t : T)
    (ht : t ∈ M.map SemidirectProduct.rightHom)
    (z : Z) (hz : z ∈ (M.comap SemidirectProduct.inl).comap ι) :
    χ t z ∈ (M.comap SemidirectProduct.inl).comap ι := by
  obtain ⟨x, hx, hr⟩ := ht
  change x.right = t at hr
  have hn := conjugate_mem_kernel φ M x hx (ι z) hz
  rw [hι] at hn
  have hc : x.left * ι (χ x.right z) = ι (χ x.right z) * x.left :=
    (Subgroup.mem_center_iff.mp (hcentral (χ x.right z))) x.left
  rw [hc, mul_assoc, mul_inv_cancel, mul_one, hr] at hn
  exact hn

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (ψ : B →* MulAut A) : Finite (A ⋊[ψ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

theorem index_factor [Finite N] [Finite T] (M : Subgroup (N ⋊[φ] T)) :
    M.index = (M.comap SemidirectProduct.inl).index *
      (M.map SemidirectProduct.rightHom).index := by
  have h := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    (SemidirectProduct.rightHom : (N ⋊[φ] T) →* T)
    SemidirectProduct.rightHom_surjective M
  have hk : (M.comap SemidirectProduct.inl).index =
      M.relIndex (SemidirectProduct.rightHom : (N ⋊[φ] T) →* T).ker := by
    rw [Subgroup.index_comap, SemidirectProduct.range_inl_eq_ker_rightHom]
  rw [← hk] at h
  exact h

/-- The central and quotient indices retain the actual intersection J.
No invariance assertion about J under the projected subgroup is needed. -/
theorem index_layer_factor [Finite N] [Finite T] [Finite V]
    (π : N →* V) (hπ : Function.Surjective π) (ι : Z →* N)
    (hexact : ι.range = π.ker) (M : Subgroup (N ⋊[φ] T)) :
    M.index = ((M.comap SemidirectProduct.inl).comap ι).index *
      ((M.comap SemidirectProduct.inl).map π).index *
        (M.map SemidirectProduct.rightHom).index := by
  have h := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    π hπ (M.comap SemidirectProduct.inl)
  have hc : ((M.comap SemidirectProduct.inl).comap ι).index =
      (M.comap SemidirectProduct.inl).relIndex π.ker := by
    rw [Subgroup.index_comap, hexact]
  rw [← hc] at h
  rw [index_factor φ M, h]

/-- Exact cardinal coupling for the same M, its central preimage C,
its quotient image W, and its projected subgroup L. -/
theorem index_mul_layer_cards [Finite N] [Finite T] [Finite V] [Finite Z]
    (π : N →* V) (hπ : Function.Surjective π) (ι : Z →* N)
    (hexact : ι.range = π.ker) (M : Subgroup (N ⋊[φ] T)) :
    M.index * Nat.card ((M.comap SemidirectProduct.inl).comap ι) *
        Nat.card ((M.comap SemidirectProduct.inl).map π) =
      Nat.card Z * Nat.card V * (M.map SemidirectProduct.rightHom).index := by
  rw [index_layer_factor φ π hπ ι hexact M]
  have hC := ((M.comap SemidirectProduct.inl).comap ι).card_mul_index
  have hW := ((M.comap SemidirectProduct.inl).map π).card_mul_index
  calc
    _ = (Nat.card ((M.comap SemidirectProduct.inl).comap ι) *
          ((M.comap SemidirectProduct.inl).comap ι).index) *
        (Nat.card ((M.comap SemidirectProduct.inl).map π) *
          ((M.comap SemidirectProduct.inl).map π).index) *
        (M.map SemidirectProduct.rightHom).index := by ring
    _ = _ := by rw [hC, hW]

end SymmetricSubgroupAsymptotics.CentralExtensionSemidirectStabilizer
