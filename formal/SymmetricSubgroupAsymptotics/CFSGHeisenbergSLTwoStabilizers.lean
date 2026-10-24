import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIndex
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
import SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-! Actual stabilizer projections for a Heisenberg semidirect SL2.
A nonzero additive vector image cannot be invariant under the whole
actual SL2 when its actual central intersection is proper. No linearity
of the stabilizer image over the coefficient field is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoStabilizers

open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSymplecticQuotient
open CFSGHeisenbergFiniteFieldIsotropy CFSGTypeASLTwoWeyl
variable {K : Type*} [Field K]

def coordinateVector (g : Element K 1) : Fin 2 → K := ![g.a 0, g.b 0]

theorem coordinateVector_conjugate (k g : Element K 1) :
    coordinateVector (k * g * k⁻¹) = coordinateVector g := by
  have he : projection (k * g * k⁻¹) = projection g := by
    rw [map_mul, map_mul, map_inv]
    rw [mul_comm (projection k) (projection g), mul_assoc, mul_inv_cancel, mul_one]
  have hv : ((k * g * k⁻¹).a, (k * g * k⁻¹).b) = (g.a, g.b) :=
    congrArg Multiplicative.toAdd he
  exact congrArg (fun v : (Fin 1 → K) × (Fin 1 → K) => ![v.1 0, v.2 0]) hv

variable (φ : SL2 (F := K) →* MulAut (Element K 1))

theorem conjugate_mem_preimage (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K)))
    (t : Element K 1 ⋊[φ] SL2 (F := K)) (ht : t ∈ M)
    (g : Element K 1) (hg : g ∈ M.comap SemidirectProduct.inl) :
    t.left * φ t.right g * t.left⁻¹ ∈ M.comap SemidirectProduct.inl := by
  change SemidirectProduct.inl (t.left * φ t.right g * t.left⁻¹) ∈ M
  have he : (SemidirectProduct.inl (t.left * φ t.right g * t.left⁻¹) :
      Element K 1 ⋊[φ] SL2 (F := K)) =
        t * SemidirectProduct.inl g * t⁻¹ := by
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

theorem coordinate_reachable_of_full_projection
    (hφ : ∀ A g, coordinateVector (φ A g) = (A⁻¹).transpose.toLin' (coordinateVector g))
    (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K)))
    (hM : M.map SemidirectProduct.rightHom = ⊤)
    (g : Element K 1) (hg : g ∈ M.comap SemidirectProduct.inl)
    (hne : coordinateVector g ≠ 0) (v : Fin 2 → K) :
    ∃ h ∈ M.comap SemidirectProduct.inl, coordinateVector h = v := by
  by_cases hv : v = 0
  · refine ⟨1, (M.comap SemidirectProduct.inl).one_mem, ?_⟩
    rw [hv]
    ext i
    fin_cases i <;> rfl
  obtain ⟨B, hB⟩ := CFSGTypeAVectorTransitivity.exists_map_nonzero
    (0 : Fin 2) 1 (by decide) (coordinateVector g) v hne hv
  let A : SL2 (F := K) := B.transpose⁻¹
  have hA : (A⁻¹).transpose = B := by
    change ((B.transpose⁻¹)⁻¹).transpose = B
    rw [inv_inv]
    apply Subtype.ext
    exact Matrix.transpose_transpose B.val
  have hAmem : A ∈ M.map SemidirectProduct.rightHom := by rw [hM]; trivial
  obtain ⟨t, ht, htr⟩ := hAmem
  have htr' : t.right = A := htr
  refine ⟨t.left * φ t.right g * t.left⁻¹,
    conjugate_mem_preimage φ M t ht g hg, ?_⟩
  rw [coordinateVector_conjugate, hφ, htr', hA, hB]

theorem projected_ne_top_of_nonzero_vector
    (hφ : ∀ A g, coordinateVector (φ A g) = (A⁻¹).transpose.toLin' (coordinateVector g))
    (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K)))
    (hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl)
    (g : Element K 1) (hg : g ∈ M.comap SemidirectProduct.inl)
    (hne : coordinateVector g ≠ 0) : M.map SemidirectProduct.rightHom ≠ ⊤ := by
  intro hM
  let J := M.comap SemidirectProduct.inl
  apply centralPreimage_ne_top J hcentre
  apply top_unique
  intro c _
  obtain ⟨u, hu, heu⟩ := coordinate_reachable_of_full_projection φ hφ M hM g hg hne ![0, c]
  obtain ⟨v, hv, hev⟩ := coordinate_reachable_of_full_projection φ hφ M hM g hg hne ![1, 0]
  have hua : u.a 0 = 0 := congrFun heu 0
  have hub : u.b 0 = c := congrFun heu 1
  have hva : v.a 0 = 1 := congrFun hev 0
  have hvb : v.b 0 = 0 := congrFun hev 1
  have hmem := vectorImage_pairing_mem J (u.a, u.b) ⟨u, hu, rfl⟩ (v.a, v.b) ⟨v, hv, rfl⟩
  change dot u.b v.a - dot v.b u.a ∈ centralPreimage J at hmem
  simpa only [dot, Fin.sum_univ_one, hua, hub, hva, hvb,
    mul_one, zero_mul, sub_zero] using hmem

end SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoStabilizers
