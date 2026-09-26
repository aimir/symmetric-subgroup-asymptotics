import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! An actual centralizer index is bounded by the possible commutators
of a fixed finite tuple. No nilpotency or generator-rank premise is needed.
The code retains the original left cosets and original normal commutator.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace CentralizerCosetCode

variable {G : Type*} [Group G] {ι : Type*} (x : ι → G)
    (D : Subgroup G)
    (hx : ∀ g i, g*x i*g⁻¹*(x i)⁻¹ ∈ D)

/-- The complete tuple of conjugation differences on each original coset. -/
def code : G ⧸ Subgroup.centralizer (Set.range x) → (ι → D) :=
  Quotient.lift (fun g i => ⟨g*x i*g⁻¹*(x i)⁻¹,hx g i⟩) (by
    intro a b hab
    funext i
    apply Subtype.ext
    have hc := (Subgroup.mem_centralizer_iff.mp
      (QuotientGroup.leftRel_apply.mp hab)) (x i) (Set.mem_range_self i)
    have he : a*x i*a⁻¹=b*x i*b⁻¹ := by
      calc
        _ = a*(x i*(a⁻¹*b))*b⁻¹ := by group
        _ = a*((a⁻¹*b)*x i)*b⁻¹ := by rw [hc]
        _ = _ := by group
    exact congrArg (fun z => z*(x i)⁻¹) he)

theorem code_injective : Function.Injective (code x D hx) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b he
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨i,rfl⟩
  have hi := congrArg Subtype.val (congrFun he i)
  change a*x i*a⁻¹*(x i)⁻¹=b*x i*b⁻¹*(x i)⁻¹ at hi
  have heq : a*x i*a⁻¹=b*x i*b⁻¹ := mul_right_cancel hi
  calc
    x i*(a⁻¹*b) = a⁻¹*(a*x i*a⁻¹)*b := by group
    _ = a⁻¹*(b*x i*b⁻¹)*b := by rw [heq]
    _ = (a⁻¹*b)*x i := by group

include hx in
/-- A finite tuple gives a bounded centralizer index even in a
nonabelian group. The original subgroup D supplies the actual value set. -/
theorem index_le [Finite G] [Finite ι] :
    (Subgroup.centralizer (Set.range x)).index ≤ (Nat.card D)^(Nat.card ι) := by
  rw [Subgroup.index_eq_card]
  have h := Nat.card_le_card_of_injective _ (code_injective x D hx)
  simpa only [Nat.card_fun] using h

end CentralizerCosetCode

/-- The exact normal subgroup used to partition original epimorphisms
once a short tuple with onto image has been fixed. -/
def generatorNormalCommutator {G : Type*} [Group G] {ι : Type*} (x : ι → G) :
    Subgroup G := ⁅Subgroup.normalClosure (Set.range x),(⊤ : Subgroup G)⁆

instance generatorNormalCommutator_normal {G : Type*} [Group G] {ι : Type*}
    (x : ι → G) : (generatorNormalCommutator x).Normal := by
  unfold generatorNormalCommutator
  infer_instance

theorem generatorNormalCommutator_le_derived {G : Type*} [Group G] {ι : Type*}
    (x : ι → G) : generatorNormalCommutator x ≤ commutator G := by
  rw [commutator_def]
  exact Subgroup.commutator_mono le_top le_rfl

/-- Every tuple commutator lies in this same original derived normal. -/
theorem tuple_commutator_mem_generatorNormalCommutator
    {G : Type*} [Group G] {ι : Type*} (x : ι → G) (g : G) (i : ι) :
    g*x i*g⁻¹*(x i)⁻¹ ∈ generatorNormalCommutator x := by
  unfold generatorNormalCommutator
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
    (Subgroup.subset_normalClosure (Set.mem_range_self i))

/-- The centralizer index consumes only a fixed tuple power of the
actual normal commutator order. -/
theorem centralizer_index_le_normalCommutator_card
    {G : Type*} [Group G] [Finite G] {ι : Type*} [Finite ι] (x : ι → G) :
    (Subgroup.centralizer (Set.range x)).index ≤
      (Nat.card (generatorNormalCommutator x))^(Nat.card ι) :=
  CentralizerCosetCode.index_le x (generatorNormalCommutator x)
    (tuple_commutator_mem_generatorNormalCommutator x)

/-- Quotienting the original source carries precisely this commutator
subgroup to the corresponding one for the actual image tuple. -/
theorem generatorNormalCommutator_map
    {G Q : Type*} [Group G] [Group Q] {ι : Type*}
    (x : ι → G) (f : G →* Q) (hf : Function.Surjective f) :
    (generatorNormalCommutator x).map f = generatorNormalCommutator (f ∘ x) := by
  unfold generatorNormalCommutator
  rw [Subgroup.map_commutator,Subgroup.map_normalClosure _ _ hf,
    Subgroup.map_top_of_surjective f hf,Set.range_comp]

end SymmetricSubgroupAsymptotics
