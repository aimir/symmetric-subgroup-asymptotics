import SymmetricSubgroupAsymptotics.TernaryHeisenbergThreeGeneratorHom

/-! Three-generator extensionality for the ACTUAL explicit Heisenberg27
coordinate group. Integer representatives of ZMod3 supply generation;
no finite group table or classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorExt
open CFSGHeisenbergCoordinateGroup TernaryCubePowerHom
abbrev P := ZMod 3
abbrev H := Element P 1
abbrev MP := Multiplicative P

def firstParameter : MP →* H where
  toFun c := ⟨fun _ => c.toAdd,0,0⟩
  map_one' := rfl
  map_mul' c d := by
    apply Element.ext
    · rfl
    · exact (zero_add (0 : Fin 1 → P)).symm
    · change 0=0+0+dot 0 (fun _ => d.toAdd)
      simp [dot]

def secondParameter : MP →* H where
  toFun c := ⟨0,fun _ => c.toAdd,0⟩
  map_one' := rfl
  map_mul' c d := by
    apply Element.ext
    · exact (zero_add (0 : Fin 1 → P)).symm
    · rfl
    · change 0=0+0+dot (fun _ => c.toAdd) 0
      simp [dot]

def first : H := firstParameter (Multiplicative.ofAdd 1)
def second : H := secondParameter (Multiplicative.ofAdd 1)
def third : H := central (Multiplicative.ofAdd 1)

theorem decomposition (h : H) :
    firstParameter (Multiplicative.ofAdd (h.a 0))*
      secondParameter (Multiplicative.ofAdd (h.b 0))*central (Multiplicative.ofAdd h.c)=h := by
  apply Element.ext
  · funext i
    change (h.a 0+0)+0=h.a i
    rw [add_zero,add_zero]
    exact congrArg h.a (Subsingleton.elim 0 i)
  · funext i
    change (0+h.b 0)+0=h.b i
    rw [zero_add,add_zero]
    exact congrArg h.b (Subsingleton.elim 0 i)
  · change (0+0+dot 0 0)+h.c+dot (0+(fun _ => h.b 0)) 0=h.c
    simp [dot]

private theorem one_generates (c : MP) :
    c=(Multiplicative.ofAdd (1 : P))^c.toAdd.val := by
  apply Multiplicative.toAdd.injective
  change c.toAdd=c.toAdd.val • (1 : P)
  simp only [nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val]

theorem parameter_hom_ext {G : Type*} [Group G] (f g : MP →* G)
    (h : f (Multiplicative.ofAdd 1)=g (Multiplicative.ofAdd 1)) : f=g := by
  apply MonoidHom.ext
  intro c
  calc
    f c = f ((Multiplicative.ofAdd (1 : P))^c.toAdd.val) := congrArg f (one_generates c)
    _ = f (Multiplicative.ofAdd 1)^c.toAdd.val := map_pow f _ _
    _ = g (Multiplicative.ofAdd 1)^c.toAdd.val := congrArg (fun x => x^c.toAdd.val) h
    _ = g ((Multiplicative.ofAdd (1 : P))^c.toAdd.val) := (map_pow g _ _).symm
    _ = g c := congrArg g (one_generates c).symm

theorem hom_ext {G : Type*} [Group G] (f g : H →* G)
    (hx : f first=g first) (hy : f second=g second) (hz : f third=g third) : f=g := by
  have hX : f.comp firstParameter=g.comp firstParameter :=
    parameter_hom_ext _ _ hx
  have hY : f.comp secondParameter=g.comp secondParameter :=
    parameter_hom_ext _ _ hy
  have hZ : f.comp (central (K := P) (m := 1))=g.comp (central (K := P) (m := 1)) :=
    parameter_hom_ext _ _ hz
  have hXv (c : MP) : f (firstParameter c)=g (firstParameter c) := DFunLike.congr_fun hX c
  have hYv (c : MP) : f (secondParameter c)=g (secondParameter c) := DFunLike.congr_fun hY c
  have hZv (c : MP) : f (central c)=g (central c) := DFunLike.congr_fun hZ c
  apply MonoidHom.ext
  intro h
  calc
    f h = f (firstParameter (Multiplicative.ofAdd (h.a 0))*
        secondParameter (Multiplicative.ofAdd (h.b 0))*central (Multiplicative.ofAdd h.c)) :=
      congrArg f (decomposition h).symm
    _ = f (firstParameter (Multiplicative.ofAdd (h.a 0)))*
        f (secondParameter (Multiplicative.ofAdd (h.b 0)))*f (central (Multiplicative.ofAdd h.c)) := by
      rw [map_mul,map_mul]
    _ = g (firstParameter (Multiplicative.ofAdd (h.a 0)))*
        g (secondParameter (Multiplicative.ofAdd (h.b 0)))*g (central (Multiplicative.ofAdd h.c)) := by
      rw [hXv,hYv,hZv]
    _ = g (firstParameter (Multiplicative.ofAdd (h.a 0))*
        secondParameter (Multiplicative.ofAdd (h.b 0))*central (Multiplicative.ofAdd h.c)) := by
      rw [map_mul,map_mul]
    _ = g h := congrArg g (decomposition h)

theorem hom_first {G : Type*} [Group G] (x y z : G)
    (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z) :
    TernaryHeisenbergThreeGeneratorHom.hom x y z hx hy hz hxz hyz hcollect first=x := by
  change powerHom x hx (Multiplicative.ofAdd 1)*powerHom y hy 1*powerHom z hz 1=x
  rw [(powerHom y hy).map_one,(powerHom z hz).map_one,mul_one,mul_one]
  exact powerHom_one x hx

theorem hom_second {G : Type*} [Group G] (x y z : G)
    (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z) :
    TernaryHeisenbergThreeGeneratorHom.hom x y z hx hy hz hxz hyz hcollect second=y := by
  change powerHom x hx 1*powerHom y hy (Multiplicative.ofAdd 1)*powerHom z hz 1=y
  rw [(powerHom x hx).map_one,(powerHom z hz).map_one,one_mul,mul_one]
  exact powerHom_one y hy

theorem hom_third {G : Type*} [Group G] (x y z : G)
    (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z) :
    TernaryHeisenbergThreeGeneratorHom.hom x y z hx hy hz hxz hyz hcollect third=z := by
  rw [third,TernaryHeisenbergThreeGeneratorHom.hom_central]
  exact powerHom_one z hz

end SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorExt
