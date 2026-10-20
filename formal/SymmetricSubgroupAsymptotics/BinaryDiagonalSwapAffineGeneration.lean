import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapPermutation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles

/-! Generator closure for the shared three-bit diagonal/swap model.
One first-block translation, the local diagonal linear group, and the
swap generate the whole model. The checked Singer orbit supplies the
translation closure uniformly for every local linear group containing it. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwap

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops

theorem hom_mem_of_closure_generators {G H I : Type} [Group G] [Group H]
    (g : I → G) (f : Subgroup.closure (Set.range g) →* H) (K : Subgroup H)
    (hg : ∀ i, f ⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩ ∈ K)
    (r : Subgroup.closure (Set.range g)) : f r ∈ K := by
  have hle : Subgroup.closure
      ((Subgroup.closure (Set.range g)).subtype ⁻¹' Set.range g) ≤ K.comap f := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨i, hi⟩ := hx
    have heq : (⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩ :
        Subgroup.closure (Set.range g)) = x := Subtype.ext hi
    exact heq ▸ hg i
  rw [Subgroup.closure_preimage_eq_top] at hle
  exact hle (Subgroup.mem_top r)

variable (R : Subgroup LinearGroup)

def affineDiagonal : R →* Model (AffineModel.linAut R) :=
  (inr : R × Binary →* Model (AffineModel.linAut R)).comp (MonoidHom.inl R Binary)

def affineFirstTranslation : Multiplicative Vector →* Model (AffineModel.linAut R) :=
  (inl : Multiplicative Vector × Multiplicative Vector →*
    Model (AffineModel.linAut R)).comp
      (MonoidHom.inl (Multiplicative Vector) (Multiplicative Vector))

private theorem affine_first_conjugate (r : R) (v : Multiplicative Vector) :
    affineDiagonal R r * affineFirstTranslation R v * (affineDiagonal R r)⁻¹ =
      affineFirstTranslation R (AffineModel.linAut R r v) := by
  change (inr (r, 1) : Model (AffineModel.linAut R)) * inl (v, 1) *
    (inr (r, 1))⁻¹ = _
  rw [conj_inl, right_inr, action_one, map_one]
  rfl

theorem affine_model_mem_of_generators (hsinger : singer ∈ R)
    (K : Subgroup (Model (AffineModel.linAut R)))
    (hlinear : ∀ r, affineDiagonal R r ∈ K)
    (ht : affineFirstTranslation R (Multiplicative.ofAdd firstVector) ∈ K)
    (hswap : (inr (1, C2Wreath.gen) : Model (AffineModel.linAut R)) ∈ K)
    (g : Model (AffineModel.linAut R)) : g ∈ K := by
  let s : R := ⟨singer, hsinger⟩
  have hfirst (v : Multiplicative Vector) : affineFirstTranslation R v ∈ K := by
    by_cases hv : Multiplicative.toAdd v = 0
    · have heq : v = 1 := Multiplicative.toAdd.injective hv
      rw [heq, map_one]
      exact K.one_mem
    obtain ⟨i, hi⟩ := singer_nonzero_orbit firstVector (Multiplicative.toAdd v)
      firstVector_ne_zero hv
    have hc := K.mul_mem (K.mul_mem (hlinear (s ^ i.val)) ht)
      (K.inv_mem (hlinear (s ^ i.val)))
    rw [affine_first_conjugate] at hc
    have heq : AffineModel.linAut R (s ^ i.val)
        (Multiplicative.ofAdd firstVector) = v := by
      apply Multiplicative.toAdd.injective
      exact hi
    exact heq ▸ hc
  have hsecond (v : Multiplicative Vector) :
      (inl (1, v) : Model (AffineModel.linAut R)) ∈ K := by
    have hc := K.mul_mem (K.mul_mem hswap (hfirst v)) (K.inv_mem hswap)
    change (inr (1, C2Wreath.gen) : Model (AffineModel.linAut R)) * inl (v, 1) *
      (inr (1, C2Wreath.gen))⁻¹ ∈ K at hc
    rw [conj_inl, right_inr, action_swap, map_one] at hc
    exact hc
  have htranslations (v : Multiplicative Vector × Multiplicative Vector) :
      (inl v : Model (AffineModel.linAut R)) ∈ K := by
    have h := K.mul_mem (hfirst v.1) (hsecond v.2)
    change (inl (v.1, 1) : Model (AffineModel.linAut R)) * inl (1, v.2) ∈ K at h
    rw [← map_mul] at h
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta] using h
  have hcomplement (r : R × Binary) :
      (inr r : Model (AffineModel.linAut R)) ∈ K := by
    rcases r with ⟨r, c⟩
    rcases C2Wreath.cases c with rfl | rfl
    · exact hlinear r
    · have h := K.mul_mem (hlinear r) hswap
      change (inr (r, 1) : Model (AffineModel.linAut R)) *
        inr (1, C2Wreath.gen) ∈ K at h
      rw [← map_mul] at h
      simpa only [Prod.mk_mul_mk, mul_one, one_mul] using h
  rw [← inl_left_mul_inr_right g]
  exact K.mul_mem (htranslations g.left) (hcomplement g.right)

end BinaryDiagonalSwap
end SymmetricSubgroupAsymptotics

end
