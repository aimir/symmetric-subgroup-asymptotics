import SymmetricSubgroupAsymptotics.PermutationCentralizerPointWords
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOne
import SymmetricSubgroupAsymptotics.BinaryRegularSixCanonicalGenerators

/-! Six original top generators have only two permutation-centralizer
candidates. The certificate uses sixteen literal point-orbit words; no
128-element top multiplication table or outer source enumeration occurs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantTopCenter
abbrev generators := BinaryRegular46FullConstantOuterCarries.generators
private def words : Fin 16 → List (Fin 6) :=
  ![[],[4,3],[4],[5,3],[5],[5,4,3],[5,4],[3],[0],[4,3,0],[4,0],[5,3,0],[5,0],[5,4,3,0],[5,4,0],[3,0]]
private theorem word_points : ∀ x : Fin 16,pointWordPermutation generators (words x) 0=x := by decide +kernel
private theorem candidate_test : ∀ y : Fin 16,
    (∀ i : Fin 6,∀ x : Fin 16,pointWordPermutation generators (words (generators i x)) y=
      generators i (pointWordPermutation generators (words x) y)) → y=0 ∨ y=8 := by decide +kernel
private theorem candidate_points : ∀ x : Fin 16,
    pointWordPermutation generators (words x) 0=BinaryRegularFullConstantPlaneOne.candidate 0 x ∧
    pointWordPermutation generators (words x) 8=BinaryRegularFullConstantPlaneOne.candidate 1 x := by decide +kernel

theorem centralizer_cases (t : Equiv.Perm (Fin 16)) (ht : ∀ i,Commute t (generators i)) :
    t=BinaryRegularFullConstantPlaneOne.candidate 0 ∨
      t=BinaryRegularFullConstantPlaneOne.candidate 1 := by
  have hbase : t 0=0 ∨ t 0=8 := centralizer_base_mem_of_pointWord_candidates
    generators 0 words word_points {y | y=0 ∨ y=8} candidate_test t ht
  rcases hbase with hbase | hbase
  · left
    apply Equiv.ext
    intro x
    rw [centralizer_eq_pointWord_candidate generators 0 words word_points t ht,hbase]
    exact (candidate_points x).1
  · right
    apply Equiv.ext
    intro x
    rw [centralizer_eq_pointWord_candidate generators 0 words word_points t ht,hbase]
    exact (candidate_points x).2

private theorem generator_points : ∀ i : Fin 6,∀ x : Fin 16,
    BinaryRegularSixCanonicalGenerators.generators i x=generators i x := by decide +kernel

/-- The two candidates bound the centre of the actual original top after
its proved canonical point labels, including every original element. -/
theorem canonical_regular_center_cases
    {H : Subgroup (Equiv.Perm (Fin 16))} (E : BinaryPairFrame H (Fin 8))
    (hzero : H=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (t : H) (ht : t∈Subgroup.center H) :
    E.canonicalPointLabels.permCongrHom t.val=BinaryRegularFullConstantPlaneOne.candidate 0 ∨
      E.canonicalPointLabels.permCongrHom t.val=BinaryRegularFullConstantPlaneOne.candidate 1 := by
  let c := E.canonicalPointLabels.permCongrHom
  have hclosure := BinaryRegularSixCanonicalGenerators.BinaryPairFrame.canonical_regular_six_closure E hzero hH hK
  have hgens : BinaryRegularSixCanonicalGenerators.generators=generators :=
    funext fun i => Equiv.ext (generator_points i)
  rw [hgens] at hclosure
  apply centralizer_cases
  intro i
  have hm : generators i∈H.map c := by
    rw [hclosure]
    exact Subgroup.subset_closure ⟨i,rfl⟩
  obtain ⟨u,hu,hui⟩ := hm
  have he : (t.val : Equiv.Perm (Fin 16))*u=u*t.val :=
    congrArg (fun z : H => z.val) ((Subgroup.mem_center_iff.mp ht ⟨u,hu⟩).symm)
  have hc := congrArg c he
  change c t.val*generators i=generators i*c t.val
  rw [←hui]
  simpa only [map_mul] using hc

end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantTopCenter
