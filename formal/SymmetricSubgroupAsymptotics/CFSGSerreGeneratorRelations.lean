import SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence

/-! The displayed Serre relations hold for the literal generators of the
literal rational quotient. No identification with a classical Lie algebra
or a root-space basis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

abbrev Free := FreeLieAlgebra ℚ (CartanMatrix.Generators (Fin n))

def quotientMap : Free (n := n) →ₗ⁅ℚ⁆ RationalLie A where
  __ := (CartanMatrix.Relations.toIdeal ℚ A).toSubmodule.mkQ
  map_lie' := fun {_ _} => rfl

@[simp] theorem quotientMap_of (g : CartanMatrix.Generators (Fin n)) :
    quotientMap A (FreeLieAlgebra.of ℚ g) = generator A g := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap A) :=
  Submodule.Quotient.mk_surjective _

theorem generator_lieSpan_eq_top :
    LieSubalgebra.lieSpan ℚ (RationalLie A) (Set.range (generator A)) = ⊤ :=
  lieSpan_image_of_freeLie_surjective (quotientMap A) (quotientMap_surjective A)

theorem relation_zero (r : Free (n := n)) (hr : r ∈ CartanMatrix.Relations.toSet ℚ A) :
    quotientMap A r = 0 := by
  apply LieSubmodule.Quotient.mk_eq_zero'.mpr
  exact LieSubmodule.subset_lieSpan hr

theorem generator_HH (i j : Fin n) :
    ⁅generator A (CartanMatrix.Generators.H i), generator A (CartanMatrix.Generators.H j)⁆ = 0 := by
  have h := relation_zero A (CartanMatrix.Relations.HH ℚ (i, j))
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩)))))
  change quotientMap A ⁅FreeLieAlgebra.of ℚ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℚ (CartanMatrix.Generators.H j)⁆ = 0 at h
  simpa only [LieHom.map_lie, quotientMap_of] using h

theorem generator_EF_same (i : Fin n) :
    ⁅generator A (CartanMatrix.Generators.E i), generator A (CartanMatrix.Generators.F i)⁆ = generator A (CartanMatrix.Generators.H i) := by
  have h := relation_zero A (CartanMatrix.Relations.EF ℚ (i, i))
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i), rfl⟩)))))
  simpa only [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply, if_pos rfl, if_true,
    map_sub, LieHom.map_lie, quotientMap_of, sub_eq_zero] using h

theorem generator_EF_ne (i j : Fin n) (hij : i ≠ j) :
    ⁅generator A (CartanMatrix.Generators.E i), generator A (CartanMatrix.Generators.F j)⁆ = 0 := by
  have h := relation_zero A (CartanMatrix.Relations.EF ℚ (i, j))
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩)))))
  simpa only [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply, if_neg hij,
    LieHom.map_lie, quotientMap_of] using h

theorem generator_HE (i j : Fin n) :
    ⁅generator A (CartanMatrix.Generators.H i), generator A (CartanMatrix.Generators.E j)⁆ = A i j • generator A (CartanMatrix.Generators.E j) := by
  have h := relation_zero A (CartanMatrix.Relations.HE ℚ A (i, j))
    (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))))
  simpa only [CartanMatrix.Relations.HE, Function.uncurry, Function.comp_apply, map_sub,
    LieHom.map_lie, map_zsmul, quotientMap_of, sub_eq_zero] using h

theorem generator_HF (i j : Fin n) :
    ⁅generator A (CartanMatrix.Generators.H i), generator A (CartanMatrix.Generators.F j)⁆ = -(A i j • generator A (CartanMatrix.Generators.F j)) := by
  have h := relation_zero A (CartanMatrix.Relations.HF ℚ A (i, j))
    (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩)))
  simpa only [CartanMatrix.Relations.HF, Function.uncurry, Function.comp_apply, map_add,
    LieHom.map_lie, map_zsmul, quotientMap_of, add_eq_zero_iff_eq_neg] using h

/-- Adjoint powers intertwine with every actual Lie homomorphism. -/
theorem lieHom_ad_pow_apply {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] (f : L →ₗ⁅R⁆ M) (x y : L) (k : ℕ) :
    f ((LieAlgebra.ad R L x ^ k) y) =
      (LieAlgebra.ad R M (f x) ^ k) (f y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieHom.map_lie, ih]

theorem generator_adE (i j : Fin n) :
    (LieAlgebra.ad ℚ (RationalLie A) (generator A (CartanMatrix.Generators.E i)) ^ ((-A i j).toNat + 1))
      (generator A (CartanMatrix.Generators.E j)) = 0 := by
  have h := relation_zero A (CartanMatrix.Relations.adE ℚ A (i, j))
    (Or.inl (Or.inr ⟨(i, j), rfl⟩))
  change quotientMap A ((LieAlgebra.ad ℚ (Free (n := n)) (FreeLieAlgebra.of ℚ (CartanMatrix.Generators.E i)) ^
    (-A i j).toNat) ⁅FreeLieAlgebra.of ℚ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℚ (CartanMatrix.Generators.E j)⁆) = 0 at h
  simp only [lieHom_ad_pow_apply, LieHom.map_lie, quotientMap_of] at h
  simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply] using h

theorem generator_adF (i j : Fin n) :
    (LieAlgebra.ad ℚ (RationalLie A) (generator A (CartanMatrix.Generators.F i)) ^ ((-A i j).toNat + 1))
      (generator A (CartanMatrix.Generators.F j)) = 0 := by
  have h := relation_zero A (CartanMatrix.Relations.adF ℚ A (i, j))
    (Or.inr ⟨(i, j), rfl⟩)
  change quotientMap A ((LieAlgebra.ad ℚ (Free (n := n)) (FreeLieAlgebra.of ℚ (CartanMatrix.Generators.F i)) ^
    (-A i j).toNat) ⁅FreeLieAlgebra.of ℚ (CartanMatrix.Generators.F i), FreeLieAlgebra.of ℚ (CartanMatrix.Generators.F j)⁆) = 0 at h
  simp only [lieHom_ad_pow_apply, LieHom.map_lie, quotientMap_of] at h
  simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply] using h

end SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
