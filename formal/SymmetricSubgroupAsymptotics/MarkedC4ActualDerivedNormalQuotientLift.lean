import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalSubdirectFiltration

/-! Quotient derived normal subgroups are lifted INSIDE the derived subgroup
of the original physical factor. Thus an ordinary original-action normal
budget descends without inventing an action for the quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualDerivedNormalQuotientLift

variable {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
  (q : G →* Q) (hq : Function.Surjective q)

def lift (V : Subgroup Q) : Subgroup G := V.comap q ⊓ commutator G

instance liftNormal (V : Subgroup Q) [V.Normal] : (lift q V).Normal :=
  inferInstanceAs (V.comap q ⊓ commutator G).Normal

omit [Finite G] [Finite Q] in
theorem lift_le_derived (V : Subgroup Q) : lift q V≤commutator G := inf_le_right

omit [Finite G] [Finite Q] in
include hq in
theorem map_lift (V : Subgroup Q) (hV : V≤commutator Q) : (lift q V).map q=V := by
  have hd : (commutator G).map q=commutator Q := by
    rw [map_commutator_eq,q.range_eq_top_of_surjective hq]
    rfl
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact hx.1
  · intro y hy
    have hym : y∈(commutator G).map q := by rw [hd]; exact hV hy
    obtain ⟨x,hx,hxy⟩ := hym
    exact ⟨x,⟨show q x∈V from hxy.symm ▸ hy,hx⟩,hxy⟩

include hq in
theorem normalGen_le_lift (V : Subgroup Q) [V.Normal] (hV : V≤commutator Q) :
    normalGen V≤normalGen (lift q V) := by
  calc
    normalGen V=normalGen ((lift q V).map q) :=
      congrArg normalGen (map_lift q hq V hV).symm
    _≤normalGen (lift q V) := normalGen_map_le q hq (lift q V)

include hq in
/-- The premise concerns only normal subgroups of the ORIGINAL factor. -/
theorem original_budget_descends (bound : ℝ)
    (hbound : ∀ N : Subgroup G,N.Normal →N≤commutator G →(normalGen N : ℝ)≤bound)
    (V : Subgroup Q) [V.Normal] (hV : V≤commutator Q) :
    (normalGen V : ℝ)≤bound := by
  have hle : (normalGen V : ℝ)≤normalGen (lift q V) := by
    exact_mod_cast normalGen_le_lift q hq V hV
  exact hle.trans (hbound (lift q V) inferInstance (lift_le_derived q V))

/-- The actual subdirect dependent-normal budget, with all local hypotheses
stated on original factors and with the independent tail killed literally. -/
theorem quotient_word_budget {t : ℕ} (K F : Fin t → Type)
    [∀ i,Group (K i)] [∀ i,Finite (K i)]
    [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (quotient : ∀ i,K i →* F i) (onto : ∀ i,Function.Surjective (quotient i))
    (H : Subgroup (∀ i,F i))
    (hfull : ∀ i,Function.Surjective (ActualSubdirectFiltration.coordinate F H i))
    (tail : Finset (Fin t)) (weight : Fin t → ℝ)
    (horiginal : ∀ (i : Fin t) (N : Subgroup (K i)),N.Normal →
      N≤commutator (K i) →(normalGen N : ℝ)≤weight i/4)
    (U : Subgroup H) [U.Normal] (hU : U≤commutator H)
    (hzero : ∀ i∈tail,∀ x∈U,ActualSubdirectFiltration.coordinate F H i x=1) :
    (normalGen U : ℝ)≤∑ i : Fin t,if i∈tail then 0 else weight i/4 := by
  apply ActualNormalSubdirectFiltration.derived_tail_rank_le F H U hfull tail weight hU hzero
  intro i V hVn hV
  letI : V.Normal := hVn
  exact original_budget_descends (quotient i) (onto i) (weight i/4) (horiginal i) V hV

end SymmetricSubgroupAsymptotics.MarkedC4.ActualDerivedNormalQuotientLift
