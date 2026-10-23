import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordSubgroup

/-! Actual first-coordinate homomorphisms of the six-root subgroup and
its two simple-axis complements. Their factorization supplies the local
Bruhat complement without assuming a positive-root presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveCoordinateKernels
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords CFSGGTwoPositiveSixWord
open CFSGGTwoPositiveWordSubgroup CFSGGTwoPositiveWordMultiplication
open CFSGGTwoOriginalPositiveCollecting
variable (K : Type) [Field K] [CharP K 3]

def coordinates (g : positiveWordGroup K) : Fin 6 → K := (positiveWordEquiv K).symm g

theorem modelWord_coordinates (g : positiveWordGroup K) : modelWord K (coordinates K g)=g.val :=
  congrArg (fun h : positiveWordGroup K => h.val) ((positiveWordEquiv K).apply_symm_apply g)

theorem coordinates_zero : coordinates K (1:positiveWordGroup K)=0 := by
  apply modelWord_injective K
  rw [modelWord_coordinates,modelWord_zero]
  rfl

theorem coordinates_mul (g h : positiveWordGroup K) :
    coordinates K (g*h)=productCoordinates K (coordinates K g) (coordinates K h) := by
  apply modelWord_injective K
  rw [modelWord_coordinates,←modelWord_mul,modelWord_coordinates,modelWord_coordinates]
  rfl

theorem modelWord_single (j : Fin 6) (t : K) :
    modelWord K (Pi.single j t)=positiveModel K j t := by
  fin_cases j <;> simp [modelWord,Pi.single_apply,positiveModel_zero,Fin.ext_iff]

def positiveElement (j : Fin 6) (t : K) : positiveWordGroup K :=
  ⟨positiveModel K j t,⟨Pi.single j t,modelWord_single K j t⟩⟩

theorem coordinates_positiveElement (j : Fin 6) (t : K) :
    coordinates K (positiveElement K j t)=Pi.single j t := by
  apply modelWord_injective K
  rw [modelWord_coordinates,modelWord_single]
  rfl

def simpleIndex (i : Fin 2) : Fin 6 := ⟨i.val,by omega⟩

def coordinateHom (i : Fin 2) : positiveWordGroup K →* Multiplicative K where
  toFun g := Multiplicative.ofAdd (coordinates K g (simpleIndex i))
  map_one' := by
    change Multiplicative.ofAdd (coordinates K (1:positiveWordGroup K) (simpleIndex i))=1
    rw [coordinates_zero]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (coordinates K (g*h) (simpleIndex i))=
      Multiplicative.ofAdd (coordinates K g (simpleIndex i))*
        Multiplicative.ofAdd (coordinates K h (simpleIndex i))
    rw [coordinates_mul]
    fin_cases i <;> rfl

theorem coordinateHom_positiveElement (i : Fin 2) (t : K) :
    coordinateHom K i (positiveElement K (simpleIndex i) t)=Multiplicative.ofAdd t := by
  change Multiplicative.ofAdd (coordinates K (positiveElement K (simpleIndex i) t) (simpleIndex i))=_
  rw [coordinates_positiveElement]
  simp only [Pi.single_eq_same]

/-- The actual subgroup of six-root words with one prescribed simple
coordinate zero, embedded in the whole original Model. -/
def complement (i : Fin 2) : Subgroup (Model CartanMatrix.G₂ K) :=
  (coordinateHom K i).ker.map (positiveWordGroup K).subtype

theorem complement_le_positive (i : Fin 2) : complement K i≤positiveWordGroup K := by
  rintro _ ⟨g,_,rfl⟩
  exact g.property

theorem factor_positive (i : Fin 2) (u : positiveWordGroup K) :
    ∃ v∈complement K i,∃ a : K,u.val=v*positiveModel K (simpleIndex i) a := by
  let a := coordinates K u (simpleIndex i)
  let r := positiveElement K (simpleIndex i) a
  let v := u*r⁻¹
  have hv : v∈(coordinateHom K i).ker := by
    change coordinateHom K i (u*r⁻¹)=1
    rw [map_mul,map_inv]
    change Multiplicative.ofAdd a*(coordinateHom K i
      (positiveElement K (simpleIndex i) a))⁻¹=1
    rw [coordinateHom_positiveElement,mul_inv_cancel]
  have he : u=v*r := by dsimp only [v]; group
  exact ⟨v.val,⟨v,hv,rfl⟩,a,congrArg (fun g : positiveWordGroup K => g.val) he⟩

theorem mem_complement_iff (i : Fin 2) (g : Model CartanMatrix.G₂ K) :
    g∈complement K i ↔ ∃ x,modelWord K x=g ∧ x (simpleIndex i)=0 := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨coordinates K u,modelWord_coordinates K u,?_⟩
    have he : Multiplicative.ofAdd (coordinates K u (simpleIndex i))=1 := hu
    exact congrArg (Multiplicative.toAdd : Multiplicative K → K) he
  · rintro ⟨x,hx,hzero⟩
    let u : positiveWordGroup K := ⟨modelWord K x,⟨x,rfl⟩⟩
    have hc : coordinates K u=x := by
      apply modelWord_injective K
      exact modelWord_coordinates K u
    have hu : u∈(coordinateHom K i).ker := by
      change Multiplicative.ofAdd (coordinates K u (simpleIndex i))=1
      rw [hc,hzero]
      rfl
    exact ⟨u,hu,hx⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveCoordinateKernels
