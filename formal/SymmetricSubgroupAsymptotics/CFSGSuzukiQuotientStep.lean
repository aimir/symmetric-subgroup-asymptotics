import SymmetricSubgroupAsymptotics.CFSGSolubleRadical
import SymmetricSubgroupAsymptotics.CFSGSemisimpleSolubleGeneration

/-! The characteristic-soluble-kernel step preserves the full Suzuki
witness: solubility, intravariance, self-normalization and generation by
the same two lifted conjugates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem map_comap_of_equivariant_equivs {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (a : MulAut G) (b : MulAut Q)
    (hcomm : ∀ x, b (f x) = f (a x)) (H : Subgroup Q) :
    (H.comap f).map a.toMonoidHom = (H.map b.toMonoidHom).comap f := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f y, hy, hcomm y⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    change f (a.symm x) ∈ H
    have he : b (f (a.symm x)) = f x :=
      (hcomm (a.symm x)).trans (congrArg f (a.apply_symm_apply x))
    rw [b.injective (he.trans hzx.symm)]
    exact hz

theorem intravariant_quotient_preimage {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [N.Characteristic]
    (H : Subgroup (G ⧸ N)) (hH : Intravariant H) :
    Intravariant (H.comap (QuotientGroup.mk' N)) := by
  intro a
  let q := QuotientGroup.mk' N
  have hNa : N.map a.toMonoidHom = N := Subgroup.characteristic_iff_map_eq.mp inferInstance a
  let b : MulAut (G ⧸ N) := QuotientGroup.congr N N a hNa
  obtain ⟨z, hz⟩ := hH b
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N z
  rw [← hg] at hz
  refine ⟨g, ?_⟩
  calc
    _ = (H.map b.toMonoidHom).comap q :=
      map_comap_of_equivariant_equivs q a b (fun _ => rfl) H
    _ = (H.map (MulAut.conj (q g)).toMonoidHom).comap q := by rw [hz]
    _ = _ := (map_comap_of_equivariant_equivs q (MulAut.conj g)
      (MulAut.conj (q g)) (by
        intro x
        change q g * q x * (q g)⁻¹ = q (g * x * g⁻¹)
        rw [map_mul, map_mul, map_inv]) H).symm

theorem self_normalizing_quotient_preimage {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N))
    (hH : Subgroup.normalizer (H : Set (G ⧸ N)) = H) :
    Subgroup.normalizer (H.comap (QuotientGroup.mk' N) : Set G) =
      H.comap (QuotientGroup.mk' N) := by
  rw [← Subgroup.comap_normalizer_eq_of_surjective H (QuotientGroup.mk'_surjective N), hH]

theorem suzuki_quotient_step {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [N.Characteristic] [IsSolvable N]
    (H : Subgroup (G ⧸ N)) (z : G ⧸ N) (hsol : IsSolvable H)
    (hinv : Intravariant H) (hself : Subgroup.normalizer (H : Set (G ⧸ N)) = H)
    (hgen : Subgroup.closure ((H : Set (G ⧸ N)) ∪
      H.map (MulAut.conj z).toMonoidHom) = ⊤) :
    ∃ (S : Subgroup G) (g : G), IsSolvable S ∧ Intravariant S ∧
      Subgroup.normalizer (S : Set G) = S ∧ N ≤ S ∧
        Subgroup.closure ((S : Set G) ∪ S.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let q := QuotientGroup.mk' N
  letI suzukiQuotient_subgroup : IsSolvable H := hsol
  letI suzukiQuotient_kernel : IsSolvable q.ker := by
    change IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N z
  refine ⟨H.comap q, g, soluble_comap_of_soluble_ker q H,
    intravariant_quotient_preimage N H hinv,
    self_normalizing_quotient_preimage N H hself, ?_, ?_⟩
  · intro x hx
    change q x ∈ H
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx]
    exact H.one_mem
  · apply preimage_two_conjugates_generate q (QuotientGroup.mk'_surjective N) H g
    have hg' : q g = z := hg
    rw [hg']
    exact hgen

end SymmetricSubgroupAsymptotics.CFSGReduction
