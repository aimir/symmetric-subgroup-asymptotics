import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! A literal prime-field basis is an ordinary additive-group generating
set. Every additive subgroup is genuinely stable under ZMod scalars,
so no extra field-scalar action or normal-generation argument is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeFieldBasisOrdinaryGenerators

variable (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem closure_basis {I : Type*} (b : Module.Basis I (ZMod p) V) :
    Subgroup.closure (Set.range (fun i => Multiplicative.ofAdd (b i))) = ⊤ := by
  let H : Subgroup (Multiplicative V) :=
    Subgroup.closure (Set.range (fun i => Multiplicative.ofAdd (b i)))
  let W : Submodule (ZMod p) V :=
    AddSubgroup.toZModSubmodule p (AddSubgroup.toSubgroup.symm H)
  have hW : W = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change Multiplicative.ofAdd (b i) ∈ H
    exact Subgroup.subset_closure ⟨i,rfl⟩
  apply top_unique
  intro x _
  have hx : x.toAdd ∈ W := by rw [hW]; exact Submodule.mem_top
  exact hx

theorem exists_generating_finset_of_basis {I : Type*} [Fintype I]
    (b : Module.Basis I (ZMod p) V) :
    ∃ S : Finset (Multiplicative V), Subgroup.closure (S : Set (Multiplicative V)) = ⊤ ∧
      S.card ≤ Fintype.card I := by
  let S := Finset.univ.image (fun i => Multiplicative.ofAdd (b i))
  have hS : (S : Set (Multiplicative V)) =
      Set.range (fun i => Multiplicative.ofAdd (b i)) := by
    simp only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  refine ⟨S,?_,?_⟩
  · rw [hS]
    exact closure_basis p b
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ])

theorem genRank_le_finrank [Fact p.Prime] [Module.Finite (ZMod p) V] :
    MarkedC4.genRank (Multiplicative V) ≤ Module.finrank (ZMod p) V := by
  obtain ⟨S,hS,hcard⟩ := exists_generating_finset_of_basis p
    (Module.finBasis (ZMod p) V)
  exact (MarkedC4.genRank_le hS).trans (by simpa only [Fintype.card_fin] using hcard)

end SymmetricSubgroupAsymptotics.PrimeFieldBasisOrdinaryGenerators
