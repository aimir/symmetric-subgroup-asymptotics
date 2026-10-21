import SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleRecognition
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGAutomorphismConjugacyClassAction

/-! The actual permutation-conjugation image is exactly the stabilizer
of the single-three-cycle conjugacy class, including degree six. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingConjugacyStabilizer
open CFSGAlternatingOuterAutomorphisms CFSGAlternatingThreeCycleRecognition
open CFSGAutomorphismConjugacyClassAction

/-- Transitivity of alternating conjugation on single 3-cycles reduces
preservation of the whole set to preservation of one actual element. -/
theorem preserves_of_one (n : ℕ) (hn : 5≤n)
    (f : MulAut (A n)) (g : A n) (hg : g.val.IsThreeCycle)
    (hfg : (f g).val.IsThreeCycle) :
    ∀ h : A n,h.val.IsThreeCycle→(f h).val.IsThreeCycle := by
  intro h hh
  have hc : IsConj g h := alternatingGroup.isThreeCycle_isConj
    (by simpa only [Nat.card_fin] using hn) hg hh
  have hm := f.toMonoidHom.map_isConj hc
  have hs := (alternatingGroup (Fin n)).subtype.map_isConj hm
  have he := Equiv.Perm.isConj_iff_cycleType_eq.mp hs
  change (f h).val.cycleType={3}
  exact he.symm.trans hfg.cycleType

theorem exists_permutation_conjugation_fin (n : ℕ) (hn : 5≤n)
    (f : MulAut (A n))
    (hpres : ∀ g : A n,g.val.IsThreeCycle→(f g).val.IsThreeCycle) :
    ∃ σ : Equiv.Perm (Fin n),f=permutationConjugation n σ := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let c : Fin n := ⟨2,by omega⟩
  let d : Fin n := ⟨3,by omega⟩
  have hfour : [a,b,c,d].Nodup := by simp [a,b,c,d,Fin.mk.injEq]
  exact exists_permutation_conjugation a b c d hfour f hpres

theorem permutationConjugation_range_eq_stabilizer (n : ℕ) (hn : 5≤n)
    (g : A n) (hg : g.val.IsThreeCycle) :
    (permutationConjugation n).range=
      MulAction.stabilizer (MulAut (A n)) (ConjClasses.mk g) := by
  ext f
  constructor
  · rintro ⟨σ,rfl⟩
    change ConjClasses.mk (permutationConjugation n σ g)=ConjClasses.mk g
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply IsConj.symm
    apply alternatingGroup.isConj_of (isConj_iff.mpr ⟨σ,rfl⟩)
    rw [hg.card_support,Fintype.card_fin]
    omega
  · intro hf
    change ConjClasses.mk (f g)=ConjClasses.mk g at hf
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hf
    have hs := (alternatingGroup (Fin n)).subtype.map_isConj hc
    have he := Equiv.Perm.isConj_iff_cycleType_eq.mp hs
    have hfg : (f g).val.IsThreeCycle := he.trans hg.cycleType
    obtain ⟨σ,hσ⟩ := exists_permutation_conjugation_fin n hn f
      (preserves_of_one n hn f g hg hfg)
    exact ⟨σ,hσ.symm⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingConjugacyStabilizer
