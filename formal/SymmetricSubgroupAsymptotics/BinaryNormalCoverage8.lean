import SymmetricSubgroupAsymptotics.BinaryActionCoverage8
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T1
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T2
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T3
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T4
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T5
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T6
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T7
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T8
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T9
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T10
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T11
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T15
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T16
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T17
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T19
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T20
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T21
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T30

/-! Complete width-eight original action/normal coverage. The eight
specified base actions form one branch; every other action has a checked
complete normal registry. Semantic pair/character acceptance is separate. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryNormalCoverage8
open BinaryActionRegistry8

def baseIndices : Finset (Fin 26) := {14, 18, 19, 20, 21, 22, 24, 25}

def normalCount (i : Fin 26) : ℕ := ![4, 8, 16, 6, 6, 7, 9, 7, 19, 11, 17, 20, 12, 12, 0, 12, 12, 12, 0, 0, 0, 0, 0, 13, 0, 0] i

def normals : (i : Fin 26) → Fin (normalCount i) → Subgroup (actions i) :=
  Fin.cases (letI : Group BinaryNormal8T1.Source := BinaryMenuCayley8T1.group; fun j => (BinaryNormal8T1.states j).kernel.map BinaryMenuCayley8T1.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T2.Source := BinaryMenuCayley8T2.group; fun j => (BinaryNormal8T2.states j).kernel.map BinaryMenuCayley8T2.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T3.Source := BinaryMenuCayley8T3.group; fun j => (BinaryNormal8T3.states j).kernel.map BinaryMenuCayley8T3.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T4.Source := BinaryMenuCayley8T4.group; fun j => (BinaryNormal8T4.states j).kernel.map BinaryMenuCayley8T4.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T5.Source := BinaryMenuCayley8T5.group; fun j => (BinaryNormal8T5.states j).kernel.map BinaryMenuCayley8T5.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T6.Source := BinaryMenuCayley8T6.group; fun j => (BinaryNormal8T6.states j).kernel.map BinaryMenuCayley8T6.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T7.Source := BinaryMenuCayley8T7.group; fun j => (BinaryNormal8T7.states j).kernel.map BinaryMenuCayley8T7.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T8.Source := BinaryMenuCayley8T8.group; fun j => (BinaryNormal8T8.states j).kernel.map BinaryMenuCayley8T8.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T9.Source := BinaryMenuCayley8T9.group; fun j => (BinaryNormal8T9.states j).kernel.map BinaryMenuCayley8T9.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T10.Source := BinaryMenuCayley8T10.group; fun j => (BinaryNormal8T10.states j).kernel.map BinaryMenuCayley8T10.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T11.Source := BinaryMenuCayley8T11.group; fun j => (BinaryNormal8T11.states j).kernel.map BinaryMenuCayley8T11.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T15.Source := BinaryMenuCayley8T15.group; fun j => (BinaryNormal8T15.states j).kernel.map BinaryMenuCayley8T15.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T16.Source := BinaryMenuCayley8T16.group; fun j => (BinaryNormal8T16.states j).kernel.map BinaryMenuCayley8T16.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T17.Source := BinaryMenuCayley8T17.group; fun j => (BinaryNormal8T17.states j).kernel.map BinaryMenuCayley8T17.originalEquiv.toMonoidHom) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (letI : Group BinaryNormal8T19.Source := BinaryMenuCayley8T19.group; fun j => (BinaryNormal8T19.states j).kernel.map BinaryMenuCayley8T19.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T20.Source := BinaryMenuCayley8T20.group; fun j => (BinaryNormal8T20.states j).kernel.map BinaryMenuCayley8T20.originalEquiv.toMonoidHom) (Fin.cases (letI : Group BinaryNormal8T21.Source := BinaryMenuCayley8T21.group; fun j => (BinaryNormal8T21.states j).kernel.map BinaryMenuCayley8T21.originalEquiv.toMonoidHom) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (letI : Group BinaryNormal8T30.Source := BinaryMenuCayley8T30.group; fun j => (BinaryNormal8T30.states j).kernel.map BinaryMenuCayley8T30.originalEquiv.toMonoidHom) (Fin.cases (fun j => Fin.elim0 j) (Fin.cases (fun j => Fin.elim0 j) ((fun i => Fin.elim0 i)))))))))))))))))))))))))))

theorem normalCount_sum : ∑ i : Fin 26, normalCount i=203 := by decide +kernel

theorem complete_original (i : Fin 26) (hi : i∉baseIndices)
    (N : Subgroup (actions i)) (hN : N.Normal) : ∃ j, normals i j=N := by
  fin_cases i
  · letI : Group BinaryNormal8T1.Source := BinaryMenuCayley8T1.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T1.registry _ _ BinaryNormal8T1.source_isPGroup
      BinaryMenuCayley8T1.originalEquiv N hN
  · letI : Group BinaryNormal8T2.Source := BinaryMenuCayley8T2.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T2.registry _ _ BinaryNormal8T2.source_isPGroup
      BinaryMenuCayley8T2.originalEquiv N hN
  · letI : Group BinaryNormal8T3.Source := BinaryMenuCayley8T3.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T3.registry _ _ BinaryNormal8T3.source_isPGroup
      BinaryMenuCayley8T3.originalEquiv N hN
  · letI : Group BinaryNormal8T4.Source := BinaryMenuCayley8T4.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T4.registry _ _ BinaryNormal8T4.source_isPGroup
      BinaryMenuCayley8T4.originalEquiv N hN
  · letI : Group BinaryNormal8T5.Source := BinaryMenuCayley8T5.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T5.registry _ _ BinaryNormal8T5.source_isPGroup
      BinaryMenuCayley8T5.originalEquiv N hN
  · letI : Group BinaryNormal8T6.Source := BinaryMenuCayley8T6.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T6.registry _ _ BinaryNormal8T6.source_isPGroup
      BinaryMenuCayley8T6.originalEquiv N hN
  · letI : Group BinaryNormal8T7.Source := BinaryMenuCayley8T7.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T7.registry _ _ BinaryNormal8T7.source_isPGroup
      BinaryMenuCayley8T7.originalEquiv N hN
  · letI : Group BinaryNormal8T8.Source := BinaryMenuCayley8T8.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T8.registry _ _ BinaryNormal8T8.source_isPGroup
      BinaryMenuCayley8T8.originalEquiv N hN
  · letI : Group BinaryNormal8T9.Source := BinaryMenuCayley8T9.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T9.registry _ _ BinaryNormal8T9.source_isPGroup
      BinaryMenuCayley8T9.originalEquiv N hN
  · letI : Group BinaryNormal8T10.Source := BinaryMenuCayley8T10.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T10.registry _ _ BinaryNormal8T10.source_isPGroup
      BinaryMenuCayley8T10.originalEquiv N hN
  · letI : Group BinaryNormal8T11.Source := BinaryMenuCayley8T11.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T11.registry _ _ BinaryNormal8T11.source_isPGroup
      BinaryMenuCayley8T11.originalEquiv N hN
  · letI : Group BinaryNormal8T15.Source := BinaryMenuCayley8T15.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T15.registry _ _ BinaryNormal8T15.source_isPGroup
      BinaryMenuCayley8T15.originalEquiv N hN
  · letI : Group BinaryNormal8T16.Source := BinaryMenuCayley8T16.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T16.registry _ _ BinaryNormal8T16.source_isPGroup
      BinaryMenuCayley8T16.originalEquiv N hN
  · letI : Group BinaryNormal8T17.Source := BinaryMenuCayley8T17.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T17.registry _ _ BinaryNormal8T17.source_isPGroup
      BinaryMenuCayley8T17.originalEquiv N hN
  · exact False.elim (hi (by decide +kernel))
  · letI : Group BinaryNormal8T19.Source := BinaryMenuCayley8T19.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T19.registry _ _ BinaryNormal8T19.source_isPGroup
      BinaryMenuCayley8T19.originalEquiv N hN
  · letI : Group BinaryNormal8T20.Source := BinaryMenuCayley8T20.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T20.registry _ _ BinaryNormal8T20.source_isPGroup
      BinaryMenuCayley8T20.originalEquiv N hN
  · letI : Group BinaryNormal8T21.Source := BinaryMenuCayley8T21.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T21.registry _ _ BinaryNormal8T21.source_isPGroup
      BinaryMenuCayley8T21.originalEquiv N hN
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · letI : Group BinaryNormal8T30.Source := BinaryMenuCayley8T30.group
    letI : N.Normal := hN
    exact @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _
      BinaryNormal8T30.registry _ _ BinaryNormal8T30.source_isPGroup
      BinaryMenuCayley8T30.originalEquiv N hN
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))

/-- One literal ambient conjugation transports the whole action, its
specified normal subgroup, and the original normalizer weight together. -/
theorem complete (H : Subgroup (Equiv.Perm (Fin 8))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) (N : Subgroup H) [N.Normal] :
    ∃ i : Fin 26, ∃ g : Equiv.Perm (Fin 8), ∃ hg : MulAut.conj g • H=actions i,
      (i∈baseIndices ∨ ∃ j, normals i j=actionConjugacyNormal g hg N) ∧
      Nat.card (Subgroup.normalizer (H:Set (Equiv.Perm (Fin 8))))=
        Nat.card (Subgroup.normalizer (actions i:Set (Equiv.Perm (Fin 8)))) := by
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete H hH ht
  refine ⟨i,g,hg,?_,actionConjugacy_normalizer_card g hg⟩
  by_cases hi : i∈baseIndices
  · exact Or.inl hi
  · exact Or.inr (complete_original i hi (actionConjugacyNormal g hg N) inferInstance)

end SymmetricSubgroupAsymptotics.BinaryNormalCoverage8
