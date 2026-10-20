import SymmetricSubgroupAsymptotics.OriginalKernelSectionFixedCentralizer
import SymmetricSubgroupAsymptotics.OriginalKernelSectionUniform
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.SocleActionPartQuotientKernel
import SymmetricSubgroupAsymptotics.NormalGeneratorDisjointKernelImage

/-! Actual whole-socle action rows of every original normal quotient.
The moving row lies in the retained translation kernel, and the fixed
row projects injectively to the exact retained linear quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

instance retainedOddSeparator_normal (O : Subgroup B) [O.Normal] :
    (retainedOddSeparator pi N O).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

/-- The separator's exact image in the residual linear quotient. -/
theorem retainedOddSeparator_map_base (hpi : Function.Surjective pi)
    (O : Subgroup B) :
    (retainedOddSeparator pi N O).map (base pi N)=
      O.map (sectionTop pi N hpi) := by
  apply le_antisymm
  · rintro x ⟨d,⟨g,hg,rfl⟩,rfl⟩
    refine ⟨pi g,hg,?_⟩
    exact sectionTop_apply pi N hpi g
  · rintro x ⟨b,hb,rfl⟩
    obtain ⟨g,hg⟩ := hpi b
    refine ⟨QuotientGroup.mk' N g,⟨g,?_,rfl⟩,?_⟩
    · change pi g∈O
      rw [hg]
      exact hb
    · rw [base_apply,← hg,sectionTop_apply]

variable [Finite G]

include A E in
theorem movingSocleRow_le_retainedKernel (hpi : Function.Surjective pi)
    (O : Subgroup B) [O.Normal] [IsMulCommutative O] :
    nontrivialActionSoclePart (G ⧸ N) (retainedOddSeparator pi N O) ≤
      (base pi N).ker := by
  letI : IsMulCommutative
      ((retainedOddSeparator pi N O).map (base pi N)) := by
    rw [retainedOddSeparator_map_base pi N hpi O]
    infer_instance
  exact SocleActionPartQuotientKernel.active_le_kernel (base pi N)
    (base_surjective pi N) (retainedOddSeparator pi N O)

include A E in
theorem fixedSocleRow_inf_retainedKernel (hpi : Function.Surjective pi)
    (O : Subgroup B) [O.Normal] [Finite O] [NeZero (Nat.card O : ZMod 2)]
    (hfixed : ∀ a : A, (∀ o : O, A.ρ (o : B) a=a) → a=0) :
    trivialActionSoclePart (G ⧸ N) (retainedOddSeparator pi N O) ⊓
      (base pi N).ker=⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx' : x∈(base pi N).ker ⊓ Subgroup.centralizer
      ((retainedOddSeparator pi N O) : Set (G ⧸ N)) :=
    ⟨hx.2,trivialActionSoclePart_le_centralizer _ _ hx.1⟩
  rwa [E.retainedKernel_inf_centralizer_eq_bot pi A N hpi O hfixed] at hx'

include A E in
/-- This transfers only along an injective restriction of the actual
quotient projection; it makes no subgroup-inheritance assertion. -/
theorem fixedSocleRow_normalGen_le_image (hpi : Function.Surjective pi)
    (O : Subgroup B) [O.Normal] [Finite O] [NeZero (Nat.card O : ZMod 2)]
    (hfixed : ∀ a : A, (∀ o : O, A.ρ (o : B) a=a) → a=0) :
    MarkedC4.normalGen
      (trivialActionSoclePart (G ⧸ N) (retainedOddSeparator pi N O)) ≤
    MarkedC4.normalGen
      ((trivialActionSoclePart (G ⧸ N) (retainedOddSeparator pi N O)).map (base pi N)) :=
  normalGen_le_image_of_disjoint_kernel (base pi N) (base_surjective pi N) _
    (E.fixedSocleRow_inf_retainedKernel pi A N hpi O hfixed)

variable [FiniteDimensional (ZMod 2) A]

include A E in
/-- The moving whole-socle row has two normal generators in the actual
original quotient, through its exact retained translation chart. -/
theorem movingSocleRow_normalGen_le_two (hpi : Function.Surjective pi)
    (O : Subgroup B) [O.Normal] [IsMulCommutative O]
    (hA : UniformSubrepresentationGeneratorBound A.ρ 2) :
    MarkedC4.normalGen
      (nontrivialActionSoclePart (G ⧸ N) (retainedOddSeparator pi N O))≤2 := by
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi A N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi A N)
    infer_instance
  exact (E.quotientChart pi A N).kernel_normalGen_le
    (base pi N) (E.sectionRepresentation pi A N) (base_surjective pi N) 2
    (E.sectionUniform pi A N hpi hA) _
    (E.movingSocleRow_le_retainedKernel pi A N hpi O)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
