import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalHead
import Mathlib.Data.Finset.Lattice.Fold

/-! Finite maxima of actual ambient-invariant normal heads. The derived
normal rank and the subdirect axis maximum range over literal normal
subgroups of the original groups. Attaining normals are retained, and the
subdirect bound follows from the checked original-action restriction theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The complete finite family of original normals contained in S. -/
abbrev PrimeNormalHeadIndex {H : Type*} [Group H] (S : Subgroup H) :=
  {M : Subgroup H // M.Normal ∧ M≤S}

instance primeNormalHeadIndex_normal {H : Type*} [Group H] {S : Subgroup H}
    (M : PrimeNormalHeadIndex S) : M.1.Normal := M.2.1

variable (p : ℕ) [Fact p.Prime]

/-- The value uses conjugation by the whole original ambient group. -/
def primeNormalHeadValue {H : Type*} [Group H] {S : Subgroup H}
    (M : PrimeNormalHeadIndex S) : ℕ :=
  Module.finrank (ZMod p) (primeRelativeCharacters p M.1)

/-- A maximum over all actual normals below S, not a certificate menu. -/
def primeNormalHeadMax {H : Type*} [Group H] [Finite H] (S : Subgroup H) : ℕ := by
  classical
  letI := Fintype.ofFinite (PrimeNormalHeadIndex S)
  exact (Finset.univ : Finset (PrimeNormalHeadIndex S)).sup (primeNormalHeadValue p)

theorem primeRelativeHead_le_normalHeadMax {H : Type*} [Group H] [Finite H]
    (S M : Subgroup H) [M.Normal] (hM : M≤S) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M)≤primeNormalHeadMax p S := by
  classical
  letI := Fintype.ofFinite (PrimeNormalHeadIndex S)
  exact Finset.le_sup (f := primeNormalHeadValue p)
    (Finset.mem_univ (⟨M,⟨inferInstance,hM⟩⟩ : PrimeNormalHeadIndex S))

/-- Bounding the maximum is equivalent to bounding every original normal. -/
theorem primeNormalHeadMax_le_iff {H : Type*} [Group H] [Finite H]
    (S : Subgroup H) (n : ℕ) :
    primeNormalHeadMax p S≤n ↔ ∀ (M : Subgroup H) [M.Normal], M≤S →
      Module.finrank (ZMod p) (primeRelativeCharacters p M)≤n := by
  classical
  letI := Fintype.ofFinite (PrimeNormalHeadIndex S)
  constructor
  · intro h M _ hM
    exact (primeRelativeHead_le_normalHeadMax p S M hM).trans h
  · intro h
    apply Finset.sup_le_iff.mpr
    intro M _
    exact h M.1 M.2.2

/-- Even at maximum zero there is an attaining actual normal: the index
family is nonempty because it contains the trivial subgroup. -/
theorem primeNormalHeadMax_attained {H : Type*} [Group H] [Finite H]
    (S : Subgroup H) :
    ∃ M : PrimeNormalHeadIndex S, primeNormalHeadValue p M=primeNormalHeadMax p S := by
  classical
  letI := Fintype.ofFinite (PrimeNormalHeadIndex S)
  have hnonempty : (Finset.univ : Finset (PrimeNormalHeadIndex S)).Nonempty :=
    ⟨⟨⊥,⟨inferInstance,bot_le⟩⟩,Finset.mem_univ _⟩
  obtain ⟨M,_,hM⟩ := Finset.sup_mem_of_nonempty
    (f := primeNormalHeadValue p) hnonempty
  exact ⟨M,hM⟩

theorem primeNormalHeadMax_mono {H : Type*} [Group H] [Finite H]
    {S T : Subgroup H} (hST : S≤T) : primeNormalHeadMax p S≤primeNormalHeadMax p T := by
  apply (primeNormalHeadMax_le_iff p S _).mpr
  intro M _ hM
  exact primeRelativeHead_le_normalHeadMax p T M (hM.trans hST)

/-- The maximum relative head of any actual derived normal subgroup. -/
def primeDerivedNormalRank (H : Type*) [Group H] [Finite H] : ℕ :=
  primeNormalHeadMax p (commutator H)

/-- A concrete attaining derived normal, with its original normality proof. -/
theorem primeDerivedNormalRank_attained (H : Type*) [Group H] [Finite H] :
    ∃ (M : Subgroup H) (hM : M.Normal), M≤commutator H ∧
      (letI := hM
       Module.finrank (ZMod p) (primeRelativeCharacters p M))=primeDerivedNormalRank p H := by
  obtain ⟨M,hM⟩ := primeNormalHeadMax_attained p (commutator H)
  exact ⟨M.1,M.2.1,M.2.2,hM⟩

/-- The maximum is on original normals of A inside both the actual
subdirect first axis and the actual derived subgroup of A. -/
def primeSubdirectAxisNormalRank {A B : Type*} [Group A] [Group B] [Finite A]
    (K : Subgroup (A × B)) : ℕ :=
  primeNormalHeadMax p (K.goursatFst ⊓ commutator A)

/-- Fullness on both original factors supplies the relative-head bound
for every eligible normal before taking the exact finite maximum. -/
theorem primeDerivedNormalRank_subdirect_le {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (K : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    primeDerivedNormalRank p K≤primeDerivedNormalRank p B+
      primeSubdirectAxisNormalRank p K := by
  apply (primeNormalHeadMax_le_iff p (commutator K) _).mpr
  intro M _ hM
  letI := SubdirectNormalHead.firstAxis_normal K M hA
  letI := SubdirectNormalHead.secondImage_normal K M hB
  have h := SubdirectNormalHead.relativeHead_le K M p hA hB
  have hsecond := primeRelativeHead_le_normalHeadMax p (commutator B)
    (SubdirectNormalHead.secondImage K M)
    (SubdirectNormalHead.secondImage_le_commutator K M hM)
  have hfirst := primeRelativeHead_le_normalHeadMax p (K.goursatFst ⊓ commutator A)
    (SubdirectNormalHead.firstAxis K M)
    (le_inf (SubdirectNormalHead.firstAxis_le K M)
      (SubdirectNormalHead.firstAxis_le_commutator K M hM))
  exact h.trans (Nat.add_le_add hsecond hfirst)

end SymmetricSubgroupAsymptotics
