import SymmetricSubgroupAsymptotics.FiniteIsotypicHighRows
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Data.Finite.Perm

/-! The high-isotypic quotient acts on one original simple constituent
per row. Its order is bounded by a product of small symmetric-group orders. -/
set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics

def integralModulePermutation (G S : Type) [Group G] [AddCommGroup S]
    [Module ℤ[G] S] : G →* Equiv.Perm S where
  toFun g := {
    toFun := fun x => MonoidAlgebra.of ℤ G g • x
    invFun := fun x => MonoidAlgebra.of ℤ G g⁻¹ • x
    left_inv := by
      intro x
      change MonoidAlgebra.of ℤ G g⁻¹ • (MonoidAlgebra.of ℤ G g • x)=x
      rw [← mul_smul,← map_mul,inv_mul_cancel,map_one,one_smul]
    right_inv := by
      intro x
      change MonoidAlgebra.of ℤ G g • (MonoidAlgebra.of ℤ G g⁻¹ • x)=x
      rw [← mul_smul,← map_mul,mul_inv_cancel,map_one,one_smul] }
  map_one' := by ext x; change MonoidAlgebra.of ℤ G 1 • x=x; rw [map_one,one_smul]
  map_mul' g h := by
    ext x
    change MonoidAlgebra.of ℤ G (g*h) • x=
      MonoidAlgebra.of ℤ G g • (MonoidAlgebra.of ℤ G h • x)
    rw [map_mul,mul_smul]

theorem mem_integralModulePermutation_ker
    {G S : Type} [Group G] [AddCommGroup S] [Module ℤ[G] S] (g : G) :
    g ∈ (integralModulePermutation G S).ker ↔
      ∀ x : S, MonoidAlgebra.of ℤ G g • x=x := by
  constructor
  · intro h x
    exact congrArg (fun p : Equiv.Perm S => p x) h
  · intro h
    apply Equiv.ext
    exact h

namespace FiniteIsotypicRowData

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ[G] M]
    (D : FiniteIsotypicRowData ℤ[G] M)

def highAction (t : ℕ) : G →* ((i : D.highIndex t) → Equiv.Perm (D.simplePart i.val)) :=
  Pi.monoidHom (fun i => integralModulePermutation G (D.simplePart i.val))

theorem highAction_ker_identity (t : ℕ) (g : G) :
    g ∈ (D.highAction t).ker ↔
      ∀ x : M, x ∈ D.highModule t → MonoidAlgebra.of ℤ G g • x=x := by
  constructor
  · intro hg x hx
    apply D.scalar_identity_on_high t _ ?_ x hx
    intro i s
    have hi : g ∈ (integralModulePermutation G (D.simplePart i.val)).ker :=
      congrFun hg i
    exact (mem_integralModulePermutation_ker g).mp hi s
  · intro hg
    change D.highAction t g=1
    funext i
    apply Equiv.ext
    intro s
    apply Subtype.ext
    have hs : (s : M) ∈ D.highModule t :=
      (le_iSup (fun i : D.highIndex t => i.val.val) i) (D.simple_le i.val s.property)
    exact hg s hs

theorem highAction_quotient_card_le [Finite G] [Finite M]
    [IsSemisimpleModule ℤ[G] M] (t B : ℕ)
    (hB : ∀ i : D.highIndex t, Nat.card (D.simplePart i.val) ≤ B) :
    Nat.card (G ⧸ (D.highAction t).ker) ≤ B.factorial ^ Nat.card (D.highIndex t) := by
  letI : Module.Finite ℤ[G] M := Module.Finite.of_finite
  letI : Fintype (D.highIndex t) := Fintype.ofFinite _
  let f := D.highAction t
  calc
    Nat.card (G ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    _ ≤ Nat.card ((i : D.highIndex t) → Equiv.Perm (D.simplePart i.val)) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = ∏ i : D.highIndex t, (Nat.card (D.simplePart i.val)).factorial := by
      rw [Nat.card_pi]
      simp only [Nat.card_perm]
    _ ≤ ∏ _i : D.highIndex t, B.factorial :=
      Finset.prod_le_prod' (fun i _ => Nat.factorial_le (hB i))
    _ = B.factorial ^ Nat.card (D.highIndex t) := by
      rw [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card]

end FiniteIsotypicRowData
end SymmetricSubgroupAsymptotics
