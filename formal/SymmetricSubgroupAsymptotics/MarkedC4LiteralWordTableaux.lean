import SymmetricSubgroupAsymptotics.MarkedC4FiniteBinaryWordTargets

/-! Literal upper/lower coordinate tableaux (RDT Definition3.4).
All entries are constructed from the SAME actual subdirect subgroup.
Normality and row monotonicity are proved; no tableau/count data is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.LiteralWordTableaux
open FiniteOrbitWordShapes FiniteBinaryWordTargets

variable {C b : ℕ} (T : Target C b)
abbrev Position := Fin T.shape.length.val

def coordinate (i : Position T) : T.image →* T.letters i :=
  (Pi.evalMonoidHom (fun j => T.letters j) i).comp T.image.subtype

def zeroKernel (S : Finset (Position T)) : Subgroup T.image :=
  ⨅ k : {i : Position T // i ∈ S},(coordinate T k.val).ker

theorem mem_zeroKernel (S : Finset (Position T)) (g : T.image) :
    g ∈ zeroKernel T S ↔ ∀ k ∈ S,coordinate T k g=1 := by
  simp only [zeroKernel,Subgroup.mem_iInf,MonoidHom.mem_ker,Subtype.forall]

instance zeroKernel_normal (S : Finset (Position T)) : (zeroKernel T S).Normal :=
  Subgroup.normal_iInf_normal (fun _ => inferInstance)

theorem zeroKernel_antitone {S U : Finset (Position T)} (hSU : S ⊆ U) :
    zeroKernel T U ≤ zeroKernel T S := by
  intro g hg
  apply (mem_zeroKernel T S g).mpr
  intro k hk
  exact (mem_zeroKernel T U g).mp hg k (hSU hk)

def upperIndices (j : ℕ) : Finset (Position T) := Finset.univ.filter (fun k => j<k.val)
def lowerIndices (i : Position T) (j : ℕ) : Finset (Position T) :=
  Finset.univ.filter (fun k => j≤k.val ∧ k≠i)

/-- For i≤j: (H ∩ ker(projection onto coordinates >j)) projected to i. -/
def upper (i : Position T) (j : ℕ) : Subgroup (T.letters i) :=
  (zeroKernel T (upperIndices T j)).map (coordinate T i)

/-- For j≤i: the suffix projection of H, intersected with its i-th factor;
this is represented without replacing H by a split product. -/
def lower (i : Position T) (j : ℕ) : Subgroup (T.letters i) :=
  (zeroKernel T (lowerIndices T i j)).map (coordinate T i)

theorem upper_normal (i : Position T) (j : ℕ) : (upper T i j).Normal :=
  Subgroup.Normal.map inferInstance (coordinate T i) (T.subdirect i)

theorem lower_normal (i : Position T) (j : ℕ) : (lower T i j).Normal :=
  Subgroup.Normal.map inferInstance (coordinate T i) (T.subdirect i)

/-- The two ACTUAL constructions have the same literal diagonal subgroup. -/
theorem diagonal_eq (i : Position T) : upper T i i.val=lower T i i.val := by
  have hs : upperIndices T i.val=lowerIndices T i i.val := by
    ext k
    simp only [upperIndices,lowerIndices,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      refine ⟨Nat.le_of_lt h,?_⟩
      intro he
      subst k
      omega
    · rintro ⟨h,he⟩
      have hv : k.val≠i.val := fun hv => he (Fin.ext hv)
      omega
  exact congrArg (fun S => (zeroKernel T S).map (coordinate T i)) hs

theorem upper_mono (i : Position T) {j k : ℕ} (hjk : j≤k) :
    upper T i j ≤ upper T i k := by
  apply Subgroup.map_mono
  apply zeroKernel_antitone
  intro a ha
  simp only [upperIndices,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  omega

theorem lower_mono (i : Position T) {j k : ℕ} (hjk : j≤k) :
    lower T i j ≤ lower T i k := by
  apply Subgroup.map_mono
  apply zeroKernel_antitone
  intro a ha
  simp only [lowerIndices,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  exact ⟨hjk.trans ha.1,ha.2⟩

/-- The last upper entry is the full actual factor by subdirectness. -/
theorem upper_full (i : Position T) : upper T i T.shape.length.val=⊤ := by
  have hs : upperIndices T T.shape.length.val=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hp := (Finset.mem_filter.mp hk).2
    have hkl := k.isLt
    omega
  have hk : zeroKernel T (∅ : Finset (Position T))=⊤ := by
    ext g
    simp [mem_zeroKernel]
  unfold upper
  rw [hs,hk]
  exact Subgroup.map_top_of_surjective (coordinate T i) (T.subdirect i)

end SymmetricSubgroupAsymptotics.MarkedC4.LiteralWordTableaux
