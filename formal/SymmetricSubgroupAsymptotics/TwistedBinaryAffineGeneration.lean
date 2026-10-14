import SymmetricSubgroupAsymptotics.PairedFormSwapAffinePermutation
import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffineGeneration
import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffine

/-! Closure of the twisted binary affine model follows from literal local
generator pairs, one translation, and the displayed block-swap word. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PairedFormSwapAffine

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops

theorem graph_first_surjective_of_generators {I : Type}
    (g : I → LinearGroup)
    (B : Multiplicative Vector → Multiplicative Vector → ZMod 2)
    (pairs : I → Graph (AffineModel.linAut (Subgroup.closure (Set.range g))) B)
    (hpairs : ∀ i, (pairs i).val.1 =
      (⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩ : Subgroup.closure (Set.range g))) :
    Function.Surjective (PairedFormSwapComplement.first
      (localAction (AffineModel.linAut (Subgroup.closure (Set.range g)))) B) := by
  intro r
  let π := PairedFormSwapComplement.first
    (localAction (AffineModel.linAut (Subgroup.closure (Set.range g)))) B
  have hr : r ∈ π.range := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators g (MonoidHom.id _) π.range _ r
    intro i
    exact ⟨pairs i, hpairs i⟩
  exact hr

theorem graph_hom_mem_of_generators {I H : Type} [Group H]
    (g : I → LinearGroup)
    (B : Multiplicative Vector → Multiplicative Vector → ZMod 2)
    (hsep : ∀ u v, (∀ x, B x u = B x v) → u = v)
    (pairs : I → Graph (AffineModel.linAut (Subgroup.closure (Set.range g))) B)
    (hpairs : ∀ i, (pairs i).val.1 =
      (⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩ : Subgroup.closure (Set.range g)))
    (f : Graph (AffineModel.linAut (Subgroup.closure (Set.range g))) B →* H)
    (K : Subgroup H) (hK : ∀ i, f (pairs i) ∈ K)
    (p : Graph (AffineModel.linAut (Subgroup.closure (Set.range g))) B) : f p ∈ K := by
  let L := K.comap f
  let π := PairedFormSwapComplement.first
    (localAction (AffineModel.linAut (Subgroup.closure (Set.range g)))) B
  have hi : Function.Injective π :=
    PairedFormSwapComplement.first_injective _ B
      (localAction_injective _ (BinaryDiagonalSwap.affine_linAut_injective _)) hsep
  have hr (r : Subgroup.closure (Set.range g)) : r ∈ (π.comp L.subtype).range := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators g (MonoidHom.id _)
      (π.comp L.subtype).range _ r
    intro i
    exact ⟨⟨pairs i, hK i⟩, hpairs i⟩
  obtain ⟨q, hq⟩ := hr (π p)
  have heq : q.val = p := hi hq
  exact heq ▸ q.property

variable (R : Subgroup LinearGroup)
variable (B : Multiplicative Vector → Multiplicative Vector → ZMod 2)
variable (hsymm : ∀ x y, B x y = B y x)

theorem affine_model_mem_of_generators
    (s : Graph (AffineModel.linAut R) B) (hs : s.val.1.val = singer)
    (K : Subgroup (Model (AffineModel.linAut R) B hsymm))
    (hpairs : ∀ p, pairInr (AffineModel.linAut R) B hsymm p ∈ K)
    (ht : firstTranslation (AffineModel.linAut R) B hsymm
      (Multiplicative.ofAdd firstVector) ∈ K)
    (hswap : (inr (inr C2Wreath.gen) : Model (AffineModel.linAut R) B hsymm) ∈ K)
    (g : Model (AffineModel.linAut R) B hsymm) : g ∈ K := by
  have hfirst (v : Multiplicative Vector) :
      firstTranslation (AffineModel.linAut R) B hsymm v ∈ K := by
    by_cases hv : Multiplicative.toAdd v = 0
    · have hv1 : v = 1 := Multiplicative.toAdd.injective hv
      rw [hv1, map_one]
      exact K.one_mem
    obtain ⟨i, hi⟩ := singer_nonzero_orbit firstVector (Multiplicative.toAdd v)
      firstVector_ne_zero hv
    have hc := K.mul_mem (K.mul_mem (hpairs (s ^ i.val)) ht)
      (K.inv_mem (hpairs (s ^ i.val)))
    change pairInr (AffineModel.linAut R) B hsymm (s ^ i.val) * inl
      (Multiplicative.ofAdd firstVector, 1) *
      (pairInr (AffineModel.linAut R) B hsymm (s ^ i.val))⁻¹ ∈ K at hc
    rw [conj_inl] at hc
    change inl (action (AffineModel.linAut R) B hsymm
      (⟨s ^ i.val, 1⟩ : Complement (AffineModel.linAut R) B hsymm)
      (Multiplicative.ofAdd firstVector, 1)) ∈ K at hc
    rw [action_one, map_one] at hc
    have heq : AffineModel.linAut R (s ^ i.val).val.1
        (Multiplicative.ofAdd firstVector) = v := by
      apply Multiplicative.toAdd.injective
      change (s.val.1.val ^ i.val) firstVector = Multiplicative.toAdd v
      rw [hs]
      exact hi
    rw [heq] at hc
    exact hc
  have hsecond (v : Multiplicative Vector) :
      (inl (1, v) : Model (AffineModel.linAut R) B hsymm) ∈ K := by
    have hc := K.mul_mem (K.mul_mem hswap (hfirst v)) (K.inv_mem hswap)
    change (inr (inr C2Wreath.gen) : Model (AffineModel.linAut R) B hsymm) *
      inl (v, 1) * (inr (inr C2Wreath.gen))⁻¹ ∈ K at hc
    rw [conj_inl] at hc
    change inl (action (AffineModel.linAut R) B hsymm
      (⟨1, C2Wreath.gen⟩ : Complement (AffineModel.linAut R) B hsymm) (v, 1)) ∈ K at hc
    rw [action_swap] at hc
    change (inl ((AffineModel.linAut R 1) 1, (AffineModel.linAut R 1) v) :
      Model (AffineModel.linAut R) B hsymm) ∈ K at hc
    simpa only [map_one, MulAut.one_apply] using hc
  have htranslations (v : Multiplicative Vector × Multiplicative Vector) :
      (inl v : Model (AffineModel.linAut R) B hsymm) ∈ K := by
    have h := K.mul_mem (hfirst v.1) (hsecond v.2)
    change (inl (v.1, 1) : Model (AffineModel.linAut R) B hsymm) * inl (1, v.2) ∈ K at h
    rw [← map_mul] at h
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta] using h
  have hcomplement (c : Complement (AffineModel.linAut R) B hsymm) :
      (inr c : Model (AffineModel.linAut R) B hsymm) ∈ K := by
    rcases c with ⟨p, c⟩
    rcases C2Wreath.cases c with rfl | rfl
    · exact hpairs p
    · have h := K.mul_mem (hpairs p) hswap
      change (inr (inl p) : Model (AffineModel.linAut R) B hsymm) *
        inr (inr C2Wreath.gen) ∈ K at h
      rw [← map_mul, ← mk_eq_inl_mul_inr] at h
      exact h
  rw [← inl_left_mul_inr_right g]
  exact K.mul_mem (htranslations g.left) (hcomplement g.right)

end PairedFormSwapAffine
end SymmetricSubgroupAsymptotics

end
