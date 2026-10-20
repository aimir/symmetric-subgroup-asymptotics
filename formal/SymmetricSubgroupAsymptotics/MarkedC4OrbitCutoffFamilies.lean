import SymmetricSubgroupAsymptotics.MarkedC4NilpotentGenerationRelativeRow

/-! One literal bounded-orbit family is shared by the relative and product
steps. The selected retained subgroup inherits its cutoff by orbit inclusion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.OrbitCutoffFamilies

def OrbitCutoff (C : ℕ) {b : ℕ} (G : Subgroup (PermutationGroup b)) : Prop :=
  ∀ x : Fin b,Nat.card (MulAction.orbit G x)<C

theorem OrbitCutoff.mono {C b : ℕ} {K G : Subgroup (PermutationGroup b)}
    (hG : OrbitCutoff C G) (hKG : K≤G) : OrbitCutoff C K := by
  intro x
  let f : MulAction.orbit K x → MulAction.orbit G x := fun y =>
    ⟨y.1,by
      obtain ⟨g,hg⟩ := y.property
      exact ⟨⟨g.1,hKG g.2⟩,hg⟩⟩
  have hf : Function.Injective f := by
    intro y z h
    exact Subtype.ext (show y.val=z.val from congrArg (fun u : MulAction.orbit G x => u.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans_lt (hG x)

abbrev SolubleFamily (C b : ℕ) :=
  {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ OrbitCutoff C G}
abbrev NilpotentFamily (C b : ℕ) :=
  {K : Subgroup (PermutationGroup b) // Group.IsNilpotent K ∧ OrbitCutoff C K}

def solubleCount (C b r : ℕ) : ℝ :=
  ∑ G : SolubleFamily C b, (Nat.card (G.1 →* Multiplicative (ZMod 4)) : ℝ)^r
def nilpotentCount (C b r : ℕ) : ℝ :=
  ∑ K : NilpotentFamily C b, (Nat.card (K.1 →* Multiplicative (ZMod 4)) : ℝ)^r

/-- Ordinary bounded nilpotent generation constructs the EXACT relative
row whose target is the bounded nilpotent middle family used by product. -/
def relativeRow (C b l : ℕ)
    (hordinary : ∀ G : SolubleFamily C b,
      ∃ (K : Subgroup G.1) (S : Finset G.1), Group.IsNilpotent K ∧ S.card≤l ∧
        Subgroup.closure ((S : Set G.1) ∪ K)=⊤)
    (q : ℕ → ℝ)
    (hcost : (Fintype.card (⊤ : Subgroup (PermutationGroup b)) : ℝ)^l≤(2 : ℝ)^(q b)) :
    RelativeGeneratorEncodingRow (solubleCount C) (nilpotentCount C) q l b := by
  choose K S hnil hcard hgen using hordinary
  have ht : ∀ G : SolubleFamily C b, ∃ t : Fin l → G.1,
      Subgroup.closure (Set.range t ∪ K G)=⊤ :=
    fun G => NilpotentGenerationRelative.exists_padded_generating_tuple
      (K G) (S G) (hcard G) (hgen G)
  choose tuple htuple using ht
  have hP (G : SolubleFamily C b) :
      Group.IsNilpotent ((K G).map G.1.subtype) ∧
        OrbitCutoff C ((K G).map G.1.subtype) := by
    constructor
    · letI := hnil G
      exact Group.nilpotent_of_mulEquiv
        ((K G).equivMapOfInjective G.1.subtype Subtype.coe_injective)
    · apply G.2.2.mono
      rintro x ⟨k,_,rfl⟩
      exact k.property
  let R := RelativeGenerationLiteral.row (⊤ : Subgroup (PermutationGroup b))
    (fun G : SolubleFamily C b => G.1) Subtype.val_injective (fun _ => le_top)
    K tuple htuple (fun K => Group.IsNilpotent K ∧ OrbitCutoff C K) hP q hcost
  exact {
    A := R.A
    B := R.B
    X := R.X
    fintypeA := R.fintypeA
    fintypeB := R.fintypeB
    fintypeX := R.fintypeX
    source := R.source
    target := R.target
    encoding := R.encoding
    source_identity := fun _ => rfl
    target_identity := by
      intro r
      have hI : R.fintypeB = (inferInstance : Fintype (NilpotentFamily C b)) :=
        Subsingleton.elim _ _
      change nilpotentCount C b r =
        (@Finset.univ (NilpotentFamily C b) R.fintypeB).sum
          (fun z => (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r)
      rw [hI]
      rfl
    alphabet_bound := R.alphabet_bound }
end SymmetricSubgroupAsymptotics.MarkedC4.OrbitCutoffFamilies
