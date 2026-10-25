import SymmetricSubgroupAsymptotics.BinaryWeightedMultisetCodes
import SymmetricSubgroupAsymptotics.FiniteCoefficientMultisetCardinality

/-! A uniform bound for the ALREADY PROVED binary polynomial class
cover. Every selected multiset has its stated positive weight; adding
one Unit head per block embeds it in the generic coefficient code.
No selected matrix or action table is produced or expanded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryWeightedMultisetClassEnvelope
open BinaryWeightedMultisetCodes

theorem weight_eq_of_mem_codes (n : ℕ) (m : Multiset (List Bool))
    (hm : m ∈ codes n) : weight m=n := by
  classical
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    cases n with
    | zero =>
      have he : m=0 := by simpa only [codes,Finset.mem_singleton] using hm
      subst m
      rfl
    | succ n =>
      rw [codes] at hm
      obtain ⟨d,hd,hm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨l,hl,hm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hm
      have hdu : d<n+1 := Finset.mem_range.mp hd
      have hlen : l.length=d := (mem_words_iff l d).mp hl
      have hw : weight u=n-d := ih (n-d) (by omega) u hu
      simp only [weight,Multiset.map_cons,Multiset.sum_cons,hlen] at *
      omega

private def addHeads (m : Multiset (List Bool)) : Multiset (Unit × List Bool) :=
  m.map (fun l => ((),l))

private theorem weight_addHeads (m : Multiset (List Bool)) :
    FiniteCoefficientMultisetCardinality.weight (addHeads m)=weight m := by
  simp only [FiniteCoefficientMultisetCardinality.weight,weight,addHeads,
    Multiset.map_map,Function.comp_def]

private theorem addHeads_injective : Function.Injective addHeads := by
  intro m n he
  have hh := congrArg (fun u : Multiset (Unit × List Bool) => u.map Prod.snd) he
  simpa only [addHeads,Multiset.map_map,Function.comp_def,Multiset.map_id'] using hh

theorem card_codes_le (n : ℕ) (hn : 0 < n) : (codes n).card ≤ 3^(n-1) := by
  let T := {m : Multiset (Unit × List Bool) //
    FiniteCoefficientMultisetCardinality.weight m=n}
  letI : Finite T := FiniteCoefficientMultisetCardinality.finite_weight n hn
  let f : {m : Multiset (List Bool) // m ∈ codes n} → T := fun m =>
    ⟨addHeads m.val,(weight_addHeads m.val).trans (weight_eq_of_mem_codes n m.val m.property)⟩
  have hi : Function.Injective f := by
    intro m u he
    apply Subtype.ext
    exact addHeads_injective (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hi
  have hh := FiniteCoefficientMultisetCardinality.card_le (A := Unit) (B := Bool) n hn
  have ht : Nat.card T ≤ 3^(n-1) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_unique,Fintype.card_bool,
      Nat.reduceAdd,one_mul] using hh
  have hcc : (codes n).card ≤ Nat.card T := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc
  exact hcc.trans ht

end SymmetricSubgroupAsymptotics.BinaryWeightedMultisetClassEnvelope
