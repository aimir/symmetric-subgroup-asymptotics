import SymmetricSubgroupAsymptotics.AutomorphismProperSubgroupComplementAction
import SymmetricSubgroupAsymptotics.AbelianSemidirectSubgroupCentralizerBound

/-! The literal kernel intersection of an actual subgroup of an abelian
semidirect product is preserved by its OWN projected top. A translation
group of order eight with kernel intersection of order four therefore
gives that top an actual faithful four-point complement action. Its class
count is at most five and the original subgroup has at most twenty classes.
No splitting of the subgroup, top enlargement or stabilizer census occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AbelianSemidirectPlaneKernelClassBound

variable {N H : Type} [CommGroup N] [Group H]

private theorem conjugate_translation (φ : H →* MulAut N)
    (x : N ⋊[φ] H) (n : N) :
    x * SemidirectProduct.inl n * x⁻¹ = SemidirectProduct.inl (φ x.right n) := by
  apply SemidirectProduct.ext
  · change (x.left * φ x.right n) * φ (x.right * 1) (φ x.right⁻¹ x.left⁻¹) = φ x.right n
    have hcancel : φ x.right (φ x.right⁻¹ x.left⁻¹) = x.left⁻¹ := by
      simpa only [φ.map_inv x.right] using MulAut.apply_inv_self N (φ x.right) x.left⁻¹
    rw [mul_one, hcancel]
    calc
      (x.left * φ x.right n) * x.left⁻¹ = (x.left * x.left⁻¹) * φ x.right n := by ac_rfl
      _ = φ x.right n := by rw [mul_inv_cancel, one_mul]
  · change x.right * 1 * x.right⁻¹ = 1
    simp only [mul_one, mul_inv_cancel]

theorem projected_preserves_intersection (φ : H →* MulAut N)
    (L : Subgroup (N ⋊[φ] H))
    (h : ((SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype).range)
    (n : N) :
    φ h.val n ∈ L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H)) ↔
      n ∈ L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H)) := by
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
  let Q := ((SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype).range
  have forward (q : Q) (v : N) (hv : v ∈ K) : φ q.val v ∈ K := by
    obtain ⟨u, hu⟩ := q.property
    have hright : u.val.right = q.val := hu
    have hconj := L.mul_mem (L.mul_mem u.property hv) (L.inv_mem u.property)
    rw [conjugate_translation] at hconj
    change SemidirectProduct.inl (φ q.val v) ∈ L
    rw [← hright]
    exact hconj
  constructor
  · intro hn
    have hh := forward h⁻¹ (φ h.val n) hn
    change φ h.val⁻¹ (φ h.val n) ∈ K at hh
    simpa only [map_inv, MulAut.inv_apply_self] using hh
  · exact forward h n

theorem subgroup_class_card_le_twenty_of_intersection_card_four
    [Finite N] [Finite H] (hN : Nat.card N = 8)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] H))
    (hfour : Nat.card (L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))) = 4) :
    Nat.card (ConjClasses L) ≤ 20 := by
  letI : Finite (N ⋊[φ] H) := Finite.of_equiv (N × H) SemidirectProduct.equivProd.symm
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
  let π : L →* H := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
  let ρ : π.range →* MulAut N := φ.comp π.range.subtype
  have hKcard : Nat.card K = 4 := hfour
  have hKproper : K ≠ ⊤ := by
    intro he
    rw [he, Subgroup.card_top, hN] at hKcard
    omega
  have hcomplement : Nat.card {n : N // n ∉ K} = 4 := by
    have hsum : Nat.card K + Nat.card {n : N // n ∉ K} = Nat.card N := by
      rw [← Nat.card_sum]
      exact Nat.card_congr (Equiv.sumCompl (fun n : N => n ∈ K))
    omega
  have hρ : Function.Injective ρ := hφ.comp Subtype.val_injective
  have hstable : ∀ (q : π.range) (n : N), ρ q n ∈ K ↔ n ∈ K :=
    projected_preserves_intersection φ L
  have htop : Nat.card (ConjClasses π.range) ≤ 5 :=
    AutomorphismProperSubgroupComplementAction.class_card_le_five_of_complement_card_four
      K hKproper ρ hρ hstable hcomplement
  have hker : Nat.card (ConjClasses π.ker) ≤ 4 :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk π.ker _) ConjClasses.mk_surjective).trans
      ((AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection φ L).trans_eq hfour)
  exact (conjugacyClass_card_le_kernel_mul_range π).trans
    (by simpa using Nat.mul_le_mul hker htop)

end SymmetricSubgroupAsymptotics.AbelianSemidirectPlaneKernelClassBound
