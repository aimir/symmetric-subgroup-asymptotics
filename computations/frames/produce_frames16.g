# Bounded exact frames only: classified 29 four-by-four actions, 22 primitive inputs,
# and seven primitive-eight local normal menus. No TransGrp16 census.
SizeScreen([240,70]);;
Read("tops16.g");;
Run:=function()
local checks,Check,RankStar,MakeFrame,i,T,H,P,PN,z,K,den,ns,N,phi,R0,iso,rho,targets,cosets,reps,induced,R,lift,M,C,es,dims,j,g,rows,primrows,localrows,data,frames,c,obs,A,V,q,allowed,expected,affine,mu;
checks:=0;data:=[];rows:=[];primrows:=[];localrows:=[];frames:=0;
Check:=function(ok,msg)if not ok then Error(msg);fi;checks:=checks+1;end;
RankStar:=function(T)local K,den,z;z:=0;for K in NormalSubgroups(T) do den:=ClosureGroup(CommutatorSubgroup(K,T),Group(List(GeneratorsOfGroup(K),g->g^2),One(T)));z:=Maximum(z,LogInt(Index(K,den),2));od;return z;end;
targets:=[Group((1,2,3)),Group((1,2,3),(1,2))];
MakeFrame:=function(T,H,rho)
 local cosets,reps,induced,lift,R,M;
 cosets:=RightCosets(T,H);reps:=List(cosets,Representative);
 induced:=function(g)local a,i,j,h,k;a:=[1..64];for i in [1..16] do j:=Position(cosets,cosets[i]*g);h:=reps[i]*g*reps[j]^-1;for k in [1..4] do a[4*(i-1)+k]:=4*(j-1)+k^Image(rho,h);od;od;return PermList(a);end;
 lift:=function(g,i)local a,j;a:=[1..64];for j in [1..4] do a[4*i+j]:=4*i+j^g;od;return PermList(a);end;
 R:=Group(List(GeneratorsOfGroup(T),induced));M:=Group(Concatenation(List([0..15],i->[lift((1,2)(3,4),i),lift((1,3)(2,4),i)])));
 Check(Size(R)=Size(T) and Size(M)=2^32,"actual induced faithful top and original 32-dimensional binary module");Check(IsTransitive(ClosureGroup(M,R),[1..64]),"full frame is an actual transitive action");
 return [M,induced];
end;
# Every kernel of every local epimorphism is retained; same-kernel maps differ
# by global Frobenius or inner S3 conjugation, as in the proved frame reduction.
Check(Length(AffineFourDZeroClasses)=29,"proved constructive four-by-four input count");
for i in [1..29] do
 T:=AffineFourDZeroClasses[i];H:=Stabilizer(T,1);P:=SylowSubgroup(T,3);PN:=Normalizer(T,P);z:=RankStar(T);c:=0;
 for N in Filtered(NormalSubgroups(H),N->Index(H,N) in [3,6]) do
  phi:=NaturalHomomorphismByNormalSubgroup(H,N);R0:=targets[Position([3,6],Index(H,N))];iso:=IsomorphismGroups(Image(phi),R0);if iso=fail then continue;fi;rho:=CompositionMapping(iso,phi);c:=c+1;frames:=frames+1;
  q:=MakeFrame(T,H,rho);M:=q[1];induced:=q[2];C:=Centralizer(M,Group(List(GeneratorsOfGroup(P),induced)));
  es:=List(ConjugacyClasses(SylowSubgroup(PN,2)),Representative);dims:=List(es,g->LogInt(Size(Centralizer(C,induced(g))),2));j:=Position(dims,Minimum(dims));g:=es[j];
  Check(Size(P)=3 and LogInt(Size(C),2)=10,"all actual four-by-four frames have the exact odd fixed-space dimension ten");Check(g in PN and (Order(g)=1 or PrimeDivisors(Order(g))=[2]),"literal binary normalizer witness");Check(dims[j]+z<=10,"cyclic-chain-ring bound plus full relative top rank fits ten");
  Add(rows,[i,Size(T),z,Size(R0),Size(N),Size(PN),Order(g),dims[j],dims[j]+z]);Add(data,[i,N,P,g,rows[Length(rows)]]);Print("FOUR-BY-FOUR ",Last(rows),"\n");
 od;Check(c=1,"every one of the 29 exact tops has exactly one local epimorphism-kernel frame");
od;
# Explicitly classified primitive-sixteen classification, including ineligible
# tops, with exact normal-rank and stabilizer-map tests rather than order guesses.
Check(NrPrimitiveGroups(16)=22,"proved primitive-sixteen classification input count");
expected:=[80,160,240,288,320,480,576,576,960,1152,322560,5760,1920,2880,960,11520,5760,1920,960,40320,10461394944000,20922789888000];
for i in [1..22] do
 T:=PrimitiveGroup(16,i);H:=Stabilizer(T,1);z:=RankStar(T);P:=SylowSubgroup(T,3);obs:=List(Orbits(P,[1..16]),Length);c:=0;
 Check(Size(T)=expected[i] and IsPrimitive(T,[1..16]),"exact bounded primitive action input");
 for N in Filtered(NormalSubgroups(H),N->Index(H,N) in [3,6]) do
  phi:=NaturalHomomorphismByNormalSubgroup(H,N);R0:=targets[Position([3,6],Index(H,N))];iso:=IsomorphismGroups(Image(phi),R0);if iso=fail then continue;fi;rho:=CompositionMapping(iso,phi);c:=c+1;frames:=frames+1;
  q:=MakeFrame(T,H,rho);M:=q[1];induced:=q[2];A:=P;
  if i in [6,9] then g:=First(List(ConjugacyClasses(H),Representative),g->Order(g)=15);Check(g<>fail,"literal Singer fifteen-cycle in the point stabilizer");A:=Group(g);Check(SortedList(List(Orbits(A,[1..16]),Length))=[1,15],"Singer odd subgroup has original orbits one and fifteen");fi;
  C:=Centralizer(M,Group(List(GeneratorsOfGroup(A),induced)));mu:=LogInt(Size(C),2);Check(mu+z<=10,"exact odd fixed-space capacity plus relative top rank fits ten");
  if i in [6,9] then Check(mu=2,"Singer fixed-space improvement is exactly two");fi;
  Add(primrows,[i,Size(T),Size(R0),Size(N),z,Size(A),mu,mu+z]);Add(data,[29+i,N,A,(),Last(primrows)]);Print("PRIMITIVE FRAME ",Last(primrows),"\n");
 od;Print("PRIMITIVE TOP ",[i,Size(T),z,obs,c],"\n");
od;
Check(Length(primrows)=9,"nine complete literal primitive stabilizer-kernel frames");
# The seven primitive-eight components: actual Sylow orbit types and all
# local normal menus used in the graph-independent Goursat argument.
expected:=[[1,8,56],[1,8,56,168],[1,8,1344],[1,168],[1,168,336],[1,20160],[1,20160,40320]];
for i in [1..7] do
 T:=PrimitiveGroup(8,i);ns:=NormalSubgroups(T);P:=SylowSubgroup(T,3);obs:=SortedList(List(Orbits(P,[1..8]),Length));z:=RankStar(T);
 Check(SortedList(List(ns,Size))=expected[i],"complete literal primitive-eight normal menu");
 if i=1 then Check(Size(P)=1,"the degree-eight order56 component has no ternary frame above index2");else Check(obs=[1,1,3,3],"all remaining local Sylow3 orbit types give four nonfixed orbits over two blocks");fi;
 if i in [1,2,3,4,6] then Check(z=0,"all actual normal binary relative heads vanish in the perfect-or-odd-affine local types");else Check(z=1,"the two almost-simple index2 local types have relative binary rank one");fi;
 if i in [1,2,3] then V:=Socle(T);Check(Size(V)=8 and IsElementaryAbelian(V),"literal irreducible binary translation socle");Check(CommutatorSubgroup(V,T)=V and Size(Centralizer(V,T))=1,"the local binary module has no trivial simple constituent");fi;
 Add(localrows,[i,Size(T),List(ns,Size),obs,z]);Print("PRIMITIVE EIGHT LOCAL ",Last(localrows),"\n");
od;
PrintTo("frames16.g","# Literal original kernels and odd/normalizer witnesses.\nDZeroUnpairedSixteenCertificates:=",data,";;\nDZeroFourByFourRows:=",rows,";;\nDZeroPrimitiveSixteenRows:=",primrows,";;\nDZeroPrimitiveEightLocalRows:=",localrows,";;\n");
Print("PASS SIXTEEN-FRAME PRODUCER ",checks," assertions; 29 classified constructive four-by-four frames; nine primitive frames; seven complete local normal menus; no TransGrp16 census\n");
end;;Run();QUIT;
