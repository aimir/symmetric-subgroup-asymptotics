import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.GroupTheory.Index
import Mathlib.FieldTheory.Finiteness

/-! Generator bounds for a representation with a small actual acting image.
The estimate uses the cardinality of that image, rather than the order of
the original group. No semisimplicity or faithful-action premise is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

namespace ModuleGeneratedBy

/-- Restricting scalars in an actual generating tuple costs at most the
dimension of its scalar algebra for each generator. -/
theorem finrank_le_mul_algebra_finrank
    {k R M : Type} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [FiniteDimensional k R] {n : ℕ} (h : ModuleGeneratedBy R M n) :
    Module.finrank k M ≤ n * Module.finrank k R := by
  obtain ⟨v, hv⟩ := h
  let f : (Fin n → R) →ₗ[k] M :=
    (Fintype.linearCombination R v).restrictScalars k
  have hf : Function.Surjective f :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mp hv
  have hdim := f.finrank_le_finrank_of_surjective hf
  simpa only [Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using hdim

end ModuleGeneratedBy

namespace RepresentationGeneratedBy

/-- A finite acting group supplies at most one scalar orbit position per
group element and per generator. -/
theorem finrank_le_mul_card
    {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) {n : ℕ}
    (h : RepresentationGeneratedBy rho n) :
    Module.finrank k V ≤ n * Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module k[G] rho.asModule := Representation.instModuleMonoidAlgebraAsModule rho
  have hmodule : ModuleGeneratedBy k[G] rho.asModule n := h
  have hdim := hmodule.finrank_le_mul_algebra_finrank (k := k)
  rw [rho.asModuleEquiv.finrank_eq] at hdim
  simpa only [MonoidAlgebra, Module.finrank_finsupp_self,
    Nat.card_eq_fintype_card] using hdim

/-- An actual quotient of the acting group gives the sharper dimension
bound. The input tuple still generates under the original pulled-back action. -/
theorem finrank_le_mul_card_of_comp
    {k G H V : Type} [Field k] [Group G] [Group H] [Finite H]
    [AddCommGroup V] [Module k V]
    (sigma : Representation k H V) (pi : G →* H) {n : ℕ}
    (h : RepresentationGeneratedBy (sigma.comp pi) n) :
    Module.finrank k V ≤ n * Nat.card H :=
  finrank_le_mul_card sigma (of_comp sigma pi h)

/-- In particular, a cyclic row whose action factors through a group of
order at most two has underlying dimension at most two. -/
theorem finrank_le_two_of_comp_card_le_two
    {k G H V : Type} [Field k] [Group G] [Group H] [Finite H]
    [AddCommGroup V] [Module k V]
    (sigma : Representation k H V) (pi : G →* H)
    (h : RepresentationGeneratedBy (sigma.comp pi) 1)
    (hcard : Nat.card H ≤ 2) : Module.finrank k V ≤ 2 := by
  exact (finrank_le_mul_card_of_comp sigma pi h).trans (by simpa using hcard)

end RepresentationGeneratedBy

namespace ElementaryBinaryKernel

/-- A cyclic elementary binary kernel with an actual action of order at
most two has order at most four. Its extension by that same small top has
order at most eight, with no splitting assumption. -/
theorem card_le_eight_of_cyclic_small_top
    {G H Q V : Type} [Group G] [Group H] [Group Q] [Finite H] [Finite Q]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (sigma : Representation (ZMod 2) H V) (pi : G →* H)
    (hgen : RepresentationGeneratedBy (sigma.comp pi) 1)
    (hcard : Nat.card H ≤ 2)
    (top : Q →* H) (htop : Function.Surjective top)
    (kernelEquiv : top.ker ≃* Multiplicative V) : Nat.card Q ≤ 8 := by
  have hdim : Module.finrank (ZMod 2) V ≤ 2 :=
    RepresentationGeneratedBy.finrank_le_two_of_comp_card_le_two
      sigma pi hgen hcard
  have hk : Nat.card top.ker ≤ 4 := by
    rw [Nat.card_congr kernelEquiv.toEquiv]
    change Nat.card V ≤ 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans (by norm_num)
  have hprod := top.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr htop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hprod
  calc
    Nat.card Q = Nat.card top.ker * Nat.card H := hprod.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hk hcard
    _ = 8 := by norm_num

end ElementaryBinaryKernel
end SymmetricSubgroupAsymptotics
