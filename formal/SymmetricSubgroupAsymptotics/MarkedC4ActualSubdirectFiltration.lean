import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! The actual normal «prefix» filtration of a literal subdirect subgroup.
The same diagonal factor subgroups supply actual lifted normal generators.
This constructs the structural input for simultaneous abelianization columns;
no generator or column capacity is assumed as a new bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSubdirectFiltration

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))

def coordinate (i : Fin t) : H →* F i := (Pi.evalMonoidHom F i).comp H.subtype

def «prefix» (m : ℕ) : Subgroup H :=
  ⨅ i : {i : Fin t // m ≤ i.val},(coordinate F H i.val).ker

theorem mem_prefix (m : ℕ) (h : H) :
    h ∈ «prefix» F H m ↔ ∀ i : Fin t,m ≤ i.val → h.val i=1 := by
  simp only [«prefix»,Subgroup.mem_iInf,MonoidHom.mem_ker,Subtype.forall,coordinate]
  rfl

instance prefixNormal (m : ℕ) : («prefix» F H m).Normal :=
  Subgroup.normal_iInf_normal (fun _ => inferInstance)

theorem prefix_mono (m : ℕ) : «prefix» F H m≤«prefix» F H (m+1) := by
  intro h hh
  apply (mem_prefix F H (m+1) h).mpr
  intro i hi
  exact (mem_prefix F H m h).mp hh i (by omega)

theorem prefix_zero : «prefix» F H 0=⊥ := by
  apply le_antisymm _ bot_le
  intro h hh
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  funext i
  exact (mem_prefix F H 0 h).mp hh i (Nat.zero_le _)

theorem prefix_full : «prefix» F H t=⊤ := by
  apply top_unique
  intro h _
  apply (mem_prefix F H t h).mpr
  intro i hi
  exact False.elim (Nat.not_le_of_gt i.isLt hi)

def diagonal (i : Fin t) : Subgroup (F i) :=
  («prefix» F H (i.val+1)).map (coordinate F H i)

variable (hsurj : ∀ i,Function.Surjective (coordinate F H i))

instance diagonalNormal (i : Fin t) : (diagonal F H i).Normal :=
  Subgroup.Normal.map inferInstance (coordinate F H i) (hsurj i)

/-- The actual previous «prefix» is precisely large enough to contain the
kernel of the selected coordinate on the next «prefix». -/
theorem prefix_kernel (i : Fin t) (h : H)
    (hh : h ∈ «prefix» F H (i.val+1)) (hi : coordinate F H i h=1) :
    h ∈ «prefix» F H i.val := by
  apply (mem_prefix F H i.val h).mpr
  intro j hj
  by_cases he : j=i
  · subst j
    exact hi
  · have hne : j.val≠i.val := fun hv => he (Fin.ext hv)
    exact (mem_prefix F H (i.val+1) h).mp hh j (by omega)

include hsurj in
/-- Every layer has actual lifted generators of the SAME diagonal normal
subgroup. Their cardinality is its ambient normal-generator number. -/
theorem exists_layer_generators (i : Fin t) :
    ∃ S : Finset H,S.card≤normalGen (diagonal F H i) ∧
      (S : Set H) ⊆ «prefix» F H (i.val+1) ∧
      «prefix» F H (i.val+1) ≤ Subgroup.normalClosure (S : Set H) ⊔ «prefix» F H i.val := by
  letI : (diagonal F H i).Normal := diagonalNormal F H hsurj i
  obtain ⟨s,hcard,hs,hgen⟩ := normalGen_spec (diagonal F H i)
  obtain ⟨S,hS,hmem,hcl⟩ := exists_layer_lift (coordinate F H i) (hsurj i)
    («prefix» F H i.val) («prefix» F H (i.val+1))
    (prefix_kernel F H i) s hs hgen
  exact ⟨S,hS.trans_eq hcard,hmem,hcl⟩

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSubdirectFiltration
