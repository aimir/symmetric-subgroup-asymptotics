import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGCartanColumnTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan

/-! A root-lattice-trivial original Weyl word fixes every original Cartan
column. The proof transports the checked integral bipartite sign change;
it makes no good-characteristic assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartanKernel
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckFieldWeylCartan CFSGNormTwoCoordinateLatticeWord
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem wordUnit_eq_unitWord (K : Type) [Field K] (w : List (Fin r)) :
    wordUnit A hs hp b₀ s₀ K w=
      CFSGCartanColumnTransport.unitWord
        (canonicalWeyl (realizationData A hs hp b₀ s₀) K) w := by
  induction w with
  | nil=>rfl
  | cons i w ih=>simp only [wordUnit,CFSGCartanColumnTransport.unitWord,ih]

theorem word_fixes_cartan_of_lattice_identity (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (w : List (Fin r)) (hw : wordLinear A hs hp b₀ s₀ w=1) (j : (b₀).support) :
    (wordUnit A hs hp b₀ s₀ K w : Matrix
      ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
        Pi.single (.inl j) 1 := by
  have hcol : ∀i k,(canonicalWeyl (realizationData A hs hp b₀ s₀) K i : Matrix
      ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*ᵥPi.single (.inl (s₀ k)) 1=
        Pi.single (.inl (s₀ k)) 1-((|A i k|:ℤ):K) • Pi.single (.inl (s₀ i)) 1 := by
    intro i k
    simpa only [coordinate_cartan] using weyl_cartan_general A hs hp b₀ s₀ K i (s₀ k)
  have hh := CFSGCartanColumnTransport.word_fixes_cartan_of_lattice_identity
    A s₀ ε hε hA (canonicalWeyl (realizationData A hs hp b₀ s₀) K) hcol w
    (latticeWord_eq_one_of_wordLinear_eq_one A hd hs hp ho w hw) ((s₀).symm j)
  rw [wordUnit_eq_unitWord]
  simpa only [Equiv.apply_symm_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartanKernel
