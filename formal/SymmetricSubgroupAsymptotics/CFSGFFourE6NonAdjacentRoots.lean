import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
import SymmetricSubgroupAsymptotics.CFSGFourRootPathPermutation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! Nonadjacent nodes of the literal four-node F4 path have commuting
positive root charts, with independent field parameters. The statement
is first proved on actual E6 words and then mapped into ORIGINAL F4. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NonAdjacentRoots
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourE6OriginalSimpleParameters CFSGFourRootPathPermutation
open CFSGE6GeckRelativeSimpleHom CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSG.Models.Chevalley

private theorem pair_singleton_commute (K : Type) [Field K] (i j : Fin 2)
    (h : i = 0 ∨ j = 0) (a b : Multiplicative K) :
    Commute (rawPairedHom K (RingEquiv.refl K) false i a) (rawSingletonHom K false j b) := by
  have hleft : CFSGGeckSerreRepresentation.cartan E6Base E6Index (pairedNode i) (node j) = 0 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | decide | exact (by simp at h)
  have hright : CFSGGeckSerreRepresentation.cartan E6Base E6Index (pairedPartner i) (node j) = 0 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | decide | exact (by simp at h)
  exact (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index K _ _ hleft false false a.toAdd b.toAdd).mul_left
      (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K _ _ hright false false a.toAdd b.toAdd)

private theorem four_chart_nonadjacent {G : Type*} [Monoid G] (f g : Fin 4 → G)
    (hdiag : ∀ i, Commute (f i) (g i))
    (h02 : Commute (f 0) (g 2)) (h03 : Commute (f 0) (g 3))
    (h13 : Commute (f 1) (g 3)) (h20 : Commute (f 2) (g 0))
    (h30 : Commute (f 3) (g 0)) (h31 : Commute (f 3) (g 1))
    (i j : Fin 4) (h : ¬ adjacent i j) : Commute (f i) (g j) := by
  by_cases hij : i = j
  · subst j
    exact hdiag i
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | exact (h (by decide)).elim
    | exact h02
    | exact h03
    | exact h13
    | exact h20
    | exact h30
    | exact h31

theorem raw_nonadjacent_commute (K : Type) [Field K] (i j : Fin 4)
    (h : ¬ adjacent i j) (a b : Multiplicative K) :
    Commute (rawOrbitHom K (RingEquiv.refl K) false i a)
      (rawOrbitHom K (RingEquiv.refl K) false j b) :=
  four_chart_nonadjacent
    (fun k => rawOrbitHom K (RingEquiv.refl K) false k a)
    (fun k => rawOrbitHom K (RingEquiv.refl K) false k b)
    (fun k => (Commute.all a b).map (rawOrbitHom K (RingEquiv.refl K) false k))
    (pair_singleton_commute K 0 1 (Or.inl rfl) a b)
    (pair_singleton_commute K 0 0 (Or.inl rfl) a b)
    (pair_singleton_commute K 1 0 (Or.inr rfl) a b)
    (pair_singleton_commute K 0 1 (Or.inl rfl) b a).symm
    (pair_singleton_commute K 0 0 (Or.inl rfl) b a).symm
    (pair_singleton_commute K 1 0 (Or.inr rfl) b a).symm i j h

theorem original_nonadjacent_commute (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 4)
    (h : ¬ adjacent i j) (a b : Multiplicative K) :
    Commute (originalSimpleHom K false i a) (originalSimpleHom K false j b) := by
  have hJ : Commute (simpleInGenerated K false i a) (simpleInGenerated K false j b) := by
    apply Subtype.ext
    change (simpleInGenerated K false i a).val * (simpleInGenerated K false j b).val =
      (simpleInGenerated K false j b).val * (simpleInGenerated K false i a).val
    rw [simpleInGenerated_val, simpleInGenerated_val]
    exact (raw_nonadjacent_commute K i j h a b).eq
  simpa only [simpleInGenerated_original] using hJ.map (generatedToOriginal K)

end SymmetricSubgroupAsymptotics.CFSGFFourE6NonAdjacentRoots
