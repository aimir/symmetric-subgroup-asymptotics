import SymmetricSubgroupAsymptotics.MarkedC4ActualPeelNormalChains
import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordPeel

/-! Raw physical projection histories keep the same original factors and
one mark. Their isolated normals are exactly the original monotone chains,
so later normalization does not introduce another independent normal menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualRawProjectionHistory
open ActualPeelNormalChains

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)]
  (M : Type) [Group M]
abbrev Labels (S : Finset (Fin t)) := {i : Fin t // i∈S}
abbrev Ambient (S : Finset (Fin t)) := (∀ i : Labels S,F i.val) × M

def restriction (S : Finset (Fin t)) : ((∀ i,F i) × M) →* Ambient F M S where
  toFun z := ((fun i => z.1 i.val),z.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def restrictionBetween {S T : Finset (Fin t)} (hST : S⊆T) :
    Ambient F M T →* Ambient F M S where
  toFun z := ((fun i => z.1 ⟨i.val,hST i.property⟩),z.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def raw (J : Subgroup ((∀ i,F i) × M)) (S : Finset (Fin t)) :
    Subgroup (Ambient F M S) := J.map (restriction F M S)

theorem raw_full (J : Subgroup ((∀ i,F i) × M))
    (hfull : ∀ i,Function.Surjective (coordinate F J i))
    (S : Finset (Fin t)) (i : Labels S) :
    Function.Surjective (fun h : raw F M J S => h.val.1 i) := by
  intro g
  obtain ⟨h,hh⟩ := hfull i.val g
  exact ⟨⟨restriction F M S h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩

theorem raw_map (J : Subgroup ((∀ i,F i) × M))
    {S T : Finset (Fin t)} (hST : S⊆T) :
    (raw F M J T).map (restrictionBetween F M hST)=raw F M J S := by
  unfold raw
  rw [Subgroup.map_map]
  rfl

/-- Every raw-stage isolated intersection is computed in the ORIGINAL
factor, with SAME marker zero and only retained other coordinates zero. -/
theorem mem_factor_iff (J : Subgroup ((∀ i,F i) × M))
    (S : Finset (Fin t)) (i : Labels S) (g : F i.val) :
    g∈factor F J S i.val ↔ (Pi.mulSingle i g,1)∈raw F M J S := by
  constructor
  · rintro ⟨h,hh,he⟩
    refine ⟨h.val,h.property,?_⟩
    apply Prod.ext
    · funext j
      by_cases hji : j=i
      · subst j
        simpa only [restriction,Pi.mulSingle_eq_same] using he
      · have hv : j.val≠i.val := fun h => hji (Subtype.ext h)
        have ho := (Subgroup.mem_iInf.mp hh.2) ⟨j.val,j.property,hv⟩
        change h.val.1 j.val=(Pi.mulSingle i g : ∀ k : Labels S,F k.val) j
        simpa [Pi.mulSingle,hji,Ne.symm hji] using ho
    · exact hh.1
  · rintro ⟨z,hz,he⟩
    let h : J := ⟨z,hz⟩
    refine ⟨h,⟨?_,?_⟩,?_⟩
    · change z.2=1
      exact congrArg (fun w : Ambient F M S => w.2) he
    · apply Subgroup.mem_iInf.mpr
      intro j
      have hji : (⟨j.val,j.property.1⟩ : Labels S)≠i := by
        intro hj
        exact j.property.2 (congrArg Subtype.val hj)
      have hj := congrArg
        (fun w : Ambient F M S => w.1 ⟨j.val,j.property.1⟩) he
      change z.1 j.val=1
      simpa [restriction,Pi.mulSingle,hji,Ne.symm hji] using hj
    · have hi := congrArg (fun w : Ambient F M S => w.1 i) he
      change z.1 i.val=g
      simpa only [restriction,Pi.mulSingle_eq_same] using hi

end SymmetricSubgroupAsymptotics.MarkedC4.ActualRawProjectionHistory
