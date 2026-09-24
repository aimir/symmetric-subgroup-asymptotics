# Exact finite frame bindings. Data variables are supplied by run_frames.py.
# Group-catalogue completeness is the stated PrimGrp classification premise.
FrameRequire:=function(ok,msg)
 if not ok then Error(Concatenation("FRAME CERTIFICATE: ",msg));fi;
end;;
FrameRank:=function(T)
 local L,D,z;
 z:=0;
 for L in NormalSubgroups(T) do
  D:=ClosureGroup(CommutatorSubgroup(L,T),
       Group(List(GeneratorsOfGroup(L),x->x^2),One(T)));
  FrameRequire(IsNormal(T,D) and IsElementaryAbelian(L/D),"relative quotient");
  z:=Maximum(z,LogInt(Index(L,D),2));
 od;
 return z;
end;;
FrameTargets:=[Group((1,2,3)),Group((1,2,3),(1,2))];;
FrameKernels:=function(T)
 local H,out,N,phi,q,Q;
 H:=Stabilizer(T,1);out:=[];
 for N in NormalSubgroups(H) do
  q:=Index(H,N);
  if not q in [3,6] then continue;fi;
  phi:=NaturalHomomorphismByNormalSubgroup(H,N);
  Q:=FrameTargets[Position([3,6],q)];
  if IsomorphismGroups(Image(phi),Q)<>fail then Add(out,N);fi;
 od;
 return out;
end;;
BuildFrame:=function(T,N,reps,gens,images)
 local H,phi,Q,rho,cosets,s,induced,lift,M,R,blocks;
 H:=Stabilizer(T,1);s:=Index(T,H);
 Q:=FrameTargets[Position([3,6],Index(H,N))];
 if gens=fail then
  phi:=NaturalHomomorphismByNormalSubgroup(H,N);
  rho:=CompositionMapping(IsomorphismGroups(Image(phi),Q),phi);
 else
  rho:=GroupHomomorphismByImages(H,Q,gens,images);
 fi;
 FrameRequire(rho<>fail and Kernel(rho)=N and Image(rho)=Q,"literal local map");
 if reps=fail then reps:=List(RightCosets(T,H),Representative);fi;
 FrameRequire(Length(reps)=s and ForAll(reps,x->x in T),"coset representatives");
 cosets:=List(reps,x->RightCoset(H,x));
 FrameRequire(Length(Set(cosets))=s,"coset completeness");
 induced:=function(g)
  local a,i,j,h,k;
  a:=[1..4*s];
  for i in [1..s] do
   j:=Position(cosets,cosets[i]*g);h:=reps[i]*g*reps[j]^-1;
   for k in [1..4] do a[4*(i-1)+k]:=4*(j-1)+k^Image(rho,h);od;
  od;
  return PermList(a);
 end;
 lift:=function(g,i)
  local a,j;a:=[1..4*s];
  for j in [1..4] do a[4*i+j]:=4*i+j^g;od;
  return PermList(a);
 end;
 M:=Group(Concatenation(List([0..s-1],i->
          [lift((1,2)(3,4),i),lift((1,3)(2,4),i)])));
 R:=Group(List(GeneratorsOfGroup(T),induced));
 blocks:=List([0..s-1],i->[4*i+1..4*i+4]);
 FrameRequire(Size(R)=Size(T) and Size(M)=2^(2*s),"faithful induced group");
 FrameRequire(IsTransitive(ClosureGroup(M,R),[1..4*s]),"frame transitivity");
 FrameRequire(Size(Action(Stabilizer(ClosureGroup(M,R),blocks[1],OnSets),blocks[1]))
               =4*Size(Q),"exact local action");
 return [M,R,induced];
end;;

VerifyFramesEight:=function()
 local T,i,j,bs,ns,b,r,N,f,pg,vec,k,l,z,seen;
 FrameRequire(Length(FrameEightTops)=24 and Length(FrameEightBindings)=30
               and Length(FrameEightModules)=30,"eight-frame domain");
 FrameRequire(NrPrimitiveGroups(8)=7,"primitive-eight classification size");
 for i in [1..24] do
  T:=FrameEightTops[i];
  FrameRequire(IsTransitive(T,[1..8]) and not IsPGroup(T),"nonbinary top");
  for j in [i+1..24] do
   FrameRequire(not IsConjugate(SymmetricGroup(8),T,FrameEightTops[j]),"distinct tops");
  od;
  if i>17 then
   FrameRequire(IsConjugate(SymmetricGroup(8),T,PrimitiveGroup(8,i-17)),"primitive binding");
  fi;
  z:=FrameRank(T);FrameRequire(z<=2,"all-normal top bound");
  ns:=FrameKernels(T);bs:=Filtered([1..30],j->FrameEightBindings[j][1]=i);
  FrameRequire(Length(ns)=Length(bs),"complete stabilizer kernel count");
  seen:=[];
  for j in bs do
   b:=FrameEightBindings[j];r:=FrameEightModules[j];N:=b[2];
   FrameRequire(N in ns and not N in seen,"literal kernel coverage");Add(seen,N);
   FrameRequire(r{[1..5]}=[i,Size(T),Index(Stabilizer(T,1),N),Size(N),z],"frame identity");
   f:=BuildFrame(T,N,b[5],b[3],b[4]);
   FrameRequire(Group(b[6])=f[2],"stored induced generators");
   pg:=b[7];
   FrameRequire(Length(pg)=16 and Group(pg)=f[1] and ForAll(pg,x->Order(x)=2),"binary basis");
   vec:=function(a)
    local v,t;v:=();
    for t in [1..16] do if RemInt(QuoInt(a,2^(t-1)),2)=1 then v:=v*pg[t];fi;od;
    return v;
   end;
   FrameRequire(Length(r[8])=Length(b[6]),"matrix generator count");
   for k in [1..Length(b[6])] do
    FrameRequire(Length(r[8][k])=16,"matrix dimension");
    for l in [1..16] do
     FrameRequire(pg[l]^b[6][k]=vec(r[8][k][l]),"literal conjugation matrix");
    od;
   od;
   FrameRequire(r[6]=LogInt(Size(Centralizer(f[1],SylowSubgroup(f[2],3))),2),"odd fixed dimension");
  od;
 od;
 Print("PASS EIGHT-FRAME BINDINGS: 24 tops, all normal heads, 30 literal stabilizer kernels, all matrices\n");
end;;

VerifyFramesSixteen:=function()
 local i,T,z,ns,rs,r,N,A,g,f,M,C,d,row,seen,localrows,P,obs,expected;
 FrameRequire(Length(AffineFourDZeroClasses)=29
    and Length(DZeroUnpairedSixteenCertificates)=38,"sixteen-frame domain");
 FrameRequire(NrPrimitiveGroups(16)=22,"primitive-sixteen classification size");
 expected:=[80,160,240,288,320,480,576,576,960,1152,322560,5760,1920,
            2880,960,11520,5760,1920,960,40320,10461394944000,20922789888000];
 for i in [1..51] do
  if i<=29 then T:=AffineFourDZeroClasses[i];else T:=PrimitiveGroup(16,i-29);
   FrameRequire(Size(T)=expected[i-29] and IsPrimitive(T,[1..16]),"primitive input");
  fi;
  FrameRequire(IsTransitive(T,[1..16]),"actual top transitivity");
  z:=FrameRank(T);ns:=FrameKernels(T);
  rs:=Filtered(DZeroUnpairedSixteenCertificates,r->r[1]=i);
  FrameRequire(Length(rs)=Length(ns),"complete sixteen stabilizer kernel count");
  if i<=29 then FrameRequire(Length(rs)=1,"one frame per constructed top");fi;
  seen:=[];
  for r in rs do
   N:=r[2];A:=r[3];g:=r[4];row:=r[5];
   FrameRequire(N in ns and not N in seen,"sixteen literal kernel coverage");Add(seen,N);
   FrameRequire(IsSubgroup(T,A) and RemInt(Size(A),2)=1,"actual odd witness subgroup");
   f:=BuildFrame(T,N,fail,fail,fail);M:=f[1];
   C:=Centralizer(M,Group(List(GeneratorsOfGroup(A),f[3])));
   if i<=29 then
    FrameRequire(Size(A)=Size(SylowSubgroup(T,3)),"actual Sylow witness");
    FrameRequire(g in Normalizer(T,A) and (Order(g)=1 or PrimeDivisors(Order(g))=[2]),"binary normalizer witness");
    FrameRequire(LogInt(Size(C),2)=10,"complete odd fixed space");
    d:=LogInt(Size(Centralizer(C,f[3](g))),2);
    FrameRequire(row=[i,Size(T),z,Index(Stabilizer(T,1),N),Size(N),
      Size(Normalizer(T,A)),Order(g),d,d+z],"constructed-top numerical row");
   else
    FrameRequire(g=(),"odd-only primitive witness");d:=LogInt(Size(C),2);
    FrameRequire(row=[i-29,Size(T),Index(Stabilizer(T,1),N),Size(N),z,Size(A),d,d+z],"primitive numerical row");
   fi;
   FrameRequire(d+z<=10,"sixteen-block frame inequality");
  od;
 od;
 localrows:=DZeroPrimitiveEightLocalRows;
 FrameRequire(Length(localrows)=7,"all primitive-eight local components");
 for i in [1..7] do
  T:=PrimitiveGroup(8,i);P:=SylowSubgroup(T,3);
  obs:=SortedList(List(Orbits(P,[1..8]),Length));
  FrameRequire(localrows[i][1]=i and localrows[i][2]=Size(T)
   and SortedList(localrows[i][3])=SortedList(List(NormalSubgroups(T),Size))
   and localrows[i][4]=obs and localrows[i][5]=FrameRank(T),"complete local menu");
 od;
 Print("PASS SIXTEEN-FRAME WITNESSES: 29 constructed tops, 22 primitive tops, 38 literal frames, 7 complete local menus\n");
end;;
