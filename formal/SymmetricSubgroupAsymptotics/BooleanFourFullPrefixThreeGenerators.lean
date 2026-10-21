import SymmetricSubgroupAsymptotics.BinaryBooleanFourCoefficientPrefix
import SymmetricSubgroupAsymptotics.BinaryBooleanFourDerivativeWords
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators

/-! The full thirteen-coefficient prefix has three actual module
generators: the monomials with masks7,11,12. Difference words recover its
thirteen basis vectors. This excludes the dimension-thirteen endpoint
when an original module requires at least five generators. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates

def booleanDerivativeWord : List (Fin 4) → V →ₗ[ZMod 2] V
  | [] => LinearMap.id
  | i::w => (derivative i).comp (booleanDerivativeWord w)

def booleanPrefixSource (j : Fin 13) : Fin 3 :=
  if j.val<8 then 0 else if j.val<12 then 1 else 2

def booleanPrefixGenerator : Fin 3 → Fin 16 := ![7,11,12]

private theorem prefix_generator_basis : ∀ j : Fin 13,
    booleanDerivativeWord
      (derivativePath (booleanPrefixGenerator (booleanPrefixSource j)) ⟨j.val,by omega⟩)
      (Pi.single (booleanPrefixGenerator (booleanPrefixSource j)) 1) =
      prefixChart.inclusion (Pi.single j 1) := by decide +kernel

variable {A M : Type} [Ring A] [Algebra (ZMod 2) A]
    [AddCommGroup M] [Module A M] [Module (ZMod 2) M]
    [IsScalarTower (ZMod 2) A M]

omit [Algebra (ZMod 2) A] [IsScalarTower (ZMod 2) A M] in
theorem booleanDerivativeWord_realized
    (C : M →ₗ[ZMod 2] V)
    (hderivative : ∀ i : Fin 4,∀ v : M,∃ r : A,C (r • v)=derivative i (C v))
    (word : List (Fin 4)) (v : M) :
    ∃ r : A,C (r • v)=booleanDerivativeWord word (C v) := by
  induction word with
  | nil => exact ⟨1,by simp only [one_smul,booleanDerivativeWord,LinearMap.id_apply]⟩
  | cons i word ih =>
    obtain ⟨r,hr⟩ := ih
    obtain ⟨s,hs⟩ := hderivative i (r • v)
    refine ⟨s*r,?_⟩
    rw [mul_smul,hs,hr]
    rfl

theorem boolean_four_full_prefix_generatedBy_three
    (C : M →ₗ[ZMod 2] V) (hC : Function.Injective C)
    (hrange : C.range=prefixChart.space)
    (hderivative : ∀ i : Fin 4,∀ v : M,∃ r : A,C (r • v)=derivative i (C v)) :
    ModuleGeneratedBy A M 3 := by
  have hex (i : Fin 3) : ∃ v : M,C v=Pi.single (booleanPrefixGenerator i) 1 := by
    have hm : Pi.single (booleanPrefixGenerator i) (1 : ZMod 2)∈prefixChart.space := by
      apply (mem_prefixChart _).mpr
      intro j hj
      have hi : (booleanPrefixGenerator i).val<13 := by fin_cases i <;> decide
      simp only [Pi.single_apply]
      rw [if_neg (by intro he;subst j;omega)]
    rw [←hrange] at hm
    exact hm
  choose v hv using hex
  let S : Finset M := Finset.univ.image v
  let T : Submodule A M := Submodule.span A (S : Set M)
  let Tk : Submodule (ZMod 2) M := T.restrictScalars (ZMod 2)
  have hprefix : prefixChart.space≤Tk.map C := by
    apply prefixChart.le_of_basis_mem
    intro j
    obtain ⟨r,hr⟩ := booleanDerivativeWord_realized C hderivative
      (derivativePath (booleanPrefixGenerator (booleanPrefixSource j)) ⟨j.val,by omega⟩)
      (v (booleanPrefixSource j))
    rw [hv,prefix_generator_basis] at hr
    refine ⟨r • v (booleanPrefixSource j),?_,hr⟩
    exact T.smul_mem r (Submodule.subset_span (by simp [S]))
  have hspan : T=⊤ := by
    apply top_unique
    intro x _
    have hx : C x∈prefixChart.space := hrange ▸ LinearMap.mem_range_self C x
    obtain ⟨y,hy,he⟩ := hprefix hx
    exact hC he ▸ hy
  exact ModuleGeneratedBy.of_finset_card_le S hspan 3
    (Finset.card_image_le.trans (by simp))

end SymmetricSubgroupAsymptotics
