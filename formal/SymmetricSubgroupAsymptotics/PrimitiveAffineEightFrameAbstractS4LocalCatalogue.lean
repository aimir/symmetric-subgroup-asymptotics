import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport

/-!
# The unique eligible local quotient of an abstract `S₄` stabilizer

An eight-frame point stabilizer identified with the natural symmetric group
of degree four has no quotient of order three.  Every onto noncommutative
quotient of order six has the Klein four subgroup as its kernel.  Consequently
one checked local `S₃` row is the complete eligible local catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightLiteralLocalRowCatalogue

private theorem order_two_image_eq_one_of_card_three
    {L : Type*} [Group L] [Finite L]
    (hL : Nat.card L = 3) {x : L} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h3 : orderOf x ∣ 3 := by
    simpa only [hL] using orderOf_dvd_natCard x
  have h1 : orderOf x = 1 := by
    have hd : orderOf x ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
    have hgcd : Nat.gcd 2 3 = 1 := by decide
    rw [hgcd] at hd
    exact Nat.dvd_one.mp hd
  exact orderOf_eq_one_iff.mp h1

/-- The natural symmetric group of degree four has no nontrivial quotient of
order three.  The proof uses only generation by transpositions. -/
theorem naturalS4_no_order_three_quotient
    {L : Type*} [Group L] [Finite L]
    (f : Equiv.Perm (Fin 4) →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3) : False := by
  have hswap : ∀ x y : Fin 4, f (Equiv.swap x y) = 1 := by
    intro x y
    apply order_two_image_eq_one_of_card_three hL
    calc
      f (Equiv.swap x y) ^ 2 = f (Equiv.swap x y ^ 2) :=
        (map_pow f (Equiv.swap x y) 2).symm
      _ = 1 := by rw [pow_two, Equiv.swap_mul_self, map_one]
  have hall : ∀ σ : Equiv.Perm (Fin 4), f σ = 1 := by
    intro σ
    induction σ using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul σ x y hxy ih =>
        rw [map_mul, hswap, ih, mul_one]
  have hsub : Subsingleton L :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      rw [hall, hall]⟩
  have hcard : Nat.card L ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

/-- Every onto order-six quotient of natural `S₄` has the Klein four kernel.
The noncommutativity of the target is not needed for kernel uniqueness. -/
theorem naturalS4_orderSix_kernel
    {L : Type*} [Group L] [Finite L]
    (f : Equiv.Perm (Fin 4) →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 6) : f.ker = NaturalS4.klein := by
  have hker : Nat.card f.ker = 4 := by
    have hcard := f.ker.card_mul_index
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
      Nat.card_congr Subgroup.topEquiv.toEquiv] at hcard
    have hS4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num
    rw [hS4, hL] at hcard
    omega
  have hne : f.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hker
    omega
  have hle : NaturalS4.klein ≤ f.ker :=
    le_of_minimal_selfCentralizing NaturalS4.klein
      NaturalS4.klein_minimal NaturalS4.klein_selfCentralizing f.ker hne
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [NaturalS4.card_klein, hker]
    norm_num)).symm

/-- Transport the natural Klein kernel back through a source equivalence. -/
private theorem kernel_eq_comap_of_comp_equiv_kernel_eq
    {H L : Type*} [Group H] [Group L]
    (e : H ≃* Equiv.Perm (Fin 4)) (f : H →* L)
    (hf : (f.comp e.symm.toMonoidHom).ker = NaturalS4.klein) :
    f.ker = NaturalS4.klein.comap e.toMonoidHom := by
  ext x
  change f x = 1 ↔ e x ∈ NaturalS4.klein
  have hfx : f x = (f.comp e.symm.toMonoidHom) (e x) := by simp
  rw [hfx, ← MonoidHom.mem_ker, hf]

/-- A checked `S₃` quotient is the complete eligible local catalogue of an
abstract `S₄` point stabilizer. -/
noncomputable def singletonOfAbstractS4
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (R : DegreeEightLiteralLocalRow T)
    (e : MulAction.stabilizer T (0 : Fin 8) ≃* Equiv.Perm (Fin 4))
    (hRkernel :
      R.literalLocalMap.ker = NaturalS4.klein.comap e.toMonoidHom) :
    DegreeEightLiteralLocalRowCatalogue T where
  Row := Unit
  row _ := R
  complete := by
    intro L _ _ f hf hcard
    let fS4 : Equiv.Perm (Fin 4) →* L := f.comp e.symm.toMonoidHom
    have hfS4 : Function.Surjective fS4 := hf.comp e.symm.surjective
    have hL : Nat.card L = 6 := by
      rcases hcard with h3 | ⟨h6, _⟩
      · exact False.elim (naturalS4_no_order_three_quotient fS4 hfS4 h3)
      · exact h6
    have hfkernel : fS4.ker = NaturalS4.klein :=
      naturalS4_orderSix_kernel fS4 hfS4 hL
    have hkernels : f.ker = R.literalLocalMap.ker :=
      (kernel_eq_comap_of_comp_equiv_kernel_eq e f hfkernel).trans
        hRkernel.symm
    refine ⟨(), surjectiveTargetEquivOfKernelEq f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels, ?_⟩
    exact surjectiveTargetEquivOfKernelEq_comp f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels

end DegreeEightLiteralLocalRowCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
