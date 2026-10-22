import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLiftedWeylWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagram
import SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartanKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalKernel

/-! The genuine paired Weyl subgroup normalizing the actual positive group
has a soluble diagram image and a diagonal matrix kernel. No matrix-to-
lattice faithfulness or torus-kernel recognition is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLiftedNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckLiftedWeylWords
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateNormalizerDiagram CFSGCartanDiagramLinearAction
open CFSGExceptionalDiagramAutomorphisms CFSGNormTwoGeckWordLatticeSupport
open CFSGNormTwoCoordinateCartanKernel CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixSupport CFSGNormTwoGeckDiagonalKernel
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def liftedPositive (K : Type) [Field K] : Subgroup (Pair A hs hp b₀ K) :=
  liftedWeyl A hs hp b₀ s₀ K ⊓
    (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)).comap
      (MonoidHom.fst _ _)

def latticeProjection (K : Type) [Field K] :
    liftedPositive A hd hs hp ho K→*((Fin r→ℤ)≃ₗ[ℤ](Fin r→ℤ)) :=
  (MonoidHom.snd _ _).comp (liftedPositive A hd hs hp ho K).subtype

theorem latticeProjection_mem_diagram (K : Type) [Field K]
    (x : liftedPositive A hd hs hp ho K) :
    latticeProjection A hd hs hp ho K x∈diagramLinearGroup A := by
  obtain ⟨w,hw⟩ := x.property.1
  have hn : wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) := by
    have hfst : wordUnit A hs hp b₀ s₀ K w=x.val.1 := congrArg Prod.fst hw
    rw [hfst]
    exact x.property.2
  obtain ⟨σ,hroot,hA⟩ := normalizer_word_diagram A hd hs hp ho K w hn
  apply mem_diagramLinearGroup_of_simple_images A _ σ _ hA
  intro i
  change x.val.2 (Pi.single i 1)=Pi.single (σ i) 1
  rw [←congrArg Prod.snd hw]
  change wordLinear A hs hp b₀ s₀ w (s₀ i:Roots A).val=(coordinateRoot A hd (σ i)).val
  rw [wordLinear_root,hroot i]

def diagramProjection (K : Type) [Field K] :
    liftedPositive A hd hs hp ho K→*diagramLinearGroup A :=
  (latticeProjection A hd hs hp ho K).codRestrict (diagramLinearGroup A)
    (latticeProjection_mem_diagram A hd hs hp ho K)

theorem liftedPositive_soluble (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    [IsSolvable (diagramGroup A)] : IsSolvable (liftedPositive A hd hs hp ho K) := by
  let f := diagramProjection A hd hs hp ho K
  letI : IsSolvable (diagramLinearGroup A) := diagramLinearGroup_soluble A
  have hkernel : ∀x : f.ker,x.val.val.2=1 := by
    intro x
    have hx : f x.val=1 := x.property
    exact congrArg Subtype.val hx
  have hdegree : ∀x : f.ker,Supported (latticeWeight A hs hp b₀) id
      (x.val.val.1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) := by
    intro x
    obtain ⟨w,hw⟩ := x.val.property.1
    have he : wordLinear A hs hp b₀ s₀ w=1 :=
      (congrArg Prod.snd hw).trans (hkernel x)
    have hh := word_preserves_lattice_of_linear_identity A hs hp b₀ s₀ K w he
    have hfst : wordUnit A hs hp b₀ s₀ K w=x.val.val.1 := congrArg Prod.fst hw
    rw [hfst] at hh
    exact hh
  have hcartan : ∀x : f.ker,∀j : (b₀).support,
      (x.val.val.1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*ᵥ
        Pi.single (.inl j) 1=Pi.single (.inl j) 1 := by
    intro x j
    obtain ⟨w,hw⟩ := x.val.property.1
    have he : wordLinear A hs hp b₀ s₀ w=1 :=
      (congrArg Prod.snd hw).trans (hkernel x)
    have hh := word_fixes_cartan_of_lattice_identity A hd hs hp ho K ε hε hA w he j
    have hfst : wordUnit A hs hp b₀ s₀ K w=x.val.val.1 := congrArg Prod.fst hw
    rw [hfst] at hh
    exact hh
  have hfix : ∀x : f.ker,∀j, latticeWeight A hs hp b₀ j=0→
      (x.val.val.1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*ᵥ
        Pi.single j 1=Pi.single j 1 := by
    intro x j hj
    cases j with
    | inl j=>exact hcartan x j
    | inr j=>
      change j.val=0 at hj
      have hn := j.property
      rw [hj] at hn
      norm_num [integerPairing] at hn
  letI : IsSolvable f.ker := by
    apply isSolvable_of_comm
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      exact commute_of_preserves_of_fixes_zero (latticeWeight A hs hp b₀)
        (lattice_nonzero_fibres A hs hp b₀) _ _
        (hdegree x) (hdegree y) (hfix x) (hfix y)
    · change x.val.val.2*y.val.val.2=y.val.val.2*x.val.val.2
      rw [hkernel x,hkernel y]
  apply solvable_of_ker_le_range f.ker.subtype f
  intro x hx
  exact ⟨⟨x,hx⟩,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLiftedNormalizer
