# Constructive imprimitive lists + explicitly proved primitive-eight catalogue input.
SizeScreen([240,70]);;
Run:=function()
 local checks,Check,tops,labels,AddTop,a1,a2,v1,v2,v3,v4,t1,t2,sw,M4,
       d4,o4,kc,kg,kf,ds,ks,kp,kall,B4,Bs,W4,Ws,models,U,
       flips,C,A,Es,gens,top,T,E,x,y,reps,j,i,H,ns,N,K,z,den,R0,targets,
       phi,iso,rho,cosets,repscos,induced,R,lift,M,W,psyl,ceiling,es,mus,
       mu,pcmap,pc,pg,bits,mats,bases,data,rows,frames,q,expected,primrows,witnesses;
 checks:=0;witnesses:=[];tops:=[];labels:=[];frames:=0;data:=[];rows:=[];
 Check:=function(ok,msg)if not ok then Error(msg);fi;checks:=checks+1;end;
 AddTop:=function(U,label)if not ForAny(tops,T->IsConjugate(SymmetricGroup(8),U,T)) then Add(tops,U);Add(labels,label);fi;end;
 a1:=(1,2,3);a2:=(5,6,7);v1:=(1,2)(3,4);v2:=(1,3)(2,4);v3:=(5,6)(7,8);v4:=(5,7)(6,8);t1:=(1,2);t2:=(5,6);sw:=(1,5)(2,6)(3,7)(4,8);
 B4:=Group(a1,v1,v2,a2,v3,v4);Bs:=ClosureGroup(B4,Group(t1,t2));W4:=ClosureGroup(B4,Group(sw));Ws:=ClosureGroup(Bs,Group(sw));
 d4:=Group(a1*a2,v1*v3,v2*v4);o4:=Group(a1*a2^t2,v1*v3^t2,v2*v4^t2);
 kc:=Group(v1,v2,v3,v4,a1*a2);kg:=Group(v1,v2,v3,v4,a1*a2^-1);
 ds:=Group(a1*a2,v1*v3,v2*v4,t1*t2);ks:=Group(v1,v2,v3,v4,a1*a2,t1*t2);kp:=Group(a1,v1,v2,a2,v3,v4,t1*t2);
 models:=[ClosureGroup(d4,Group(sw)),ClosureGroup(o4,Group(sw)),ClosureGroup(kc,Group(sw)),ClosureGroup(kg,Group(sw)),W4,ClosureGroup(ds,Group(sw)),ClosureGroup(ks,Group(sw)),ClosureGroup(kp,Group(sw)),ClosureGroup(kp,Group(t1*sw)),Ws];
 for i in [1..10] do AddTop(models[i],Concatenation("two-four-",String(i)));od;
 Check(Length(tops)=10,"ten proved Goursat/swap constructions remain distinct");
 flips:=[(1,2),(3,4),(5,6),(7,8)];M4:=Group(flips);C:=Group(Product(flips));A:=Group(flips[1]*flips[2],flips[2]*flips[3],flips[3]*flips[4]);Es:=[Group(()),C,A,M4];
 gens:=[[(1,3,5)(2,4,6),(1,3)(2,4)(5,7)(6,8)],[(1,3,5,7)(2,4,6,8),(1,3)(2,4)]];
 models:=[];
 for j in [1..2] do top:=gens[j];for E in Es do reps:=[];
  for x in Elements(M4) do for y in Elements(M4) do
   U:=Group(Concatenation(GeneratorsOfGroup(E),[x*top[1],y*top[2]]));
   if Intersection(U,M4)=E and IsTransitive(U,[1..8]) and not ForAny(reps,T->IsConjugate(M4,U,T)) then Add(reps,U);fi;
  od;od;
  Append(models,reps);
 od;od;
 Check(Length(models)=10,"ten proved complete binary lift constructions");
 for i in [1..10] do AddTop(models[i],Concatenation("binary-four-",String(i)));od;
 Check(Length(tops)=17,"seventeen distinct imprimitive tops, exactly three overlaps");
 # The seven-entry primitive input is explicitly proved, not inferred here.
 Check(NrPrimitiveGroups(8)=7,"stable bounded primitive input count");primrows:=[];
 expected:=[[56,8,7],[168,8,21],[1344,8,168],[168,168,1],[336,168,2],[20160,20160,1],[40320,20160,2]];
 for i in [1..7] do T:=PrimitiveGroup(8,i);Check([Size(T),Size(Socle(T)),Index(T,Socle(T))]=expected[i],"exact primitive socle/quotient interface");AddTop(T,Concatenation("primitive-",String(i)));Add(primrows,expected[i]);od;
 Check(Length(tops)=24,"seventeen constructive imprimitive and seven classified primitive tops");
 targets:=[Group((1,2,3)),Group((1,2,3),(1,2))];
 for i in [1..Length(tops)] do
  T:=tops[i];H:=Stabilizer(T,1);ns:=NormalSubgroups(T);z:=0;
  for K in ns do den:=ClosureGroup(CommutatorSubgroup(K,T),Group(List(GeneratorsOfGroup(K),g->g^2),One(T)));z:=Maximum(z,LogInt(Index(K,den),2));od;
  Check(z<=2,"complete actual-top relative binary rank is at most two");
  for N in Filtered(NormalSubgroups(H),N->Index(H,N) in [3,6]) do
   phi:=NaturalHomomorphismByNormalSubgroup(H,N);R0:=targets[Position([3,6],Index(H,N))];iso:=IsomorphismGroups(Image(phi),R0);if iso=fail then continue;fi;rho:=CompositionMapping(iso,phi);frames:=frames+1;
   cosets:=RightCosets(T,H);repscos:=List(cosets,Representative);
   induced:=function(g)local a,i,j,h,k;a:=[1..32];for i in [1..8] do j:=Position(cosets,cosets[i]*g);h:=repscos[i]*g*repscos[j]^-1;for k in [1..4] do a[4*(i-1)+k]:=4*(j-1)+k^Image(rho,h);od;od;return PermList(a);end;
   R:=Group(List(GeneratorsOfGroup(T),induced));
   lift:=function(g,i)local a,j;a:=[1..32];for j in [1..4] do a[4*i+j]:=4*i+j^g;od;return PermList(a);end;
   M:=Group(Concatenation(List([0..7],i->[lift((1,2)(3,4),i),lift((1,3)(2,4),i)])));W:=ClosureGroup(M,R);
   Check(Size(R)=Size(T) and IsTransitive(W,[1..32]),"literal induced action frame");Check(Size(Action(Stabilizer(W,[1..4],OnSets),[1..4]))=4*Size(R0),"exact affine local equality");
   psyl:=SylowSubgroup(R,3);ceiling:=LogInt(Size(Centralizer(M,psyl)),2);
   es:=Filtered(NormalSubgroups(W),E->IsSubgroup(M,E));mus:=List(es,E->LogInt(Index(E,CommutatorSubgroup(E,R)),2));mu:=Maximum(mus);
   Check(mu<=2 and mu+z<=4,"complete module list gives stronger exact-frame bound");
   pcmap:=IsomorphismPcGroup(M);pc:=Pcgs(Image(pcmap));pg:=List(pc,x->PreImagesRepresentative(pcmap,x));
   bits:=x->Sum([1..16],j->ExponentsOfPcElement(pc,Image(pcmap,x))[j]*2^(j-1));
   mats:=List(GeneratorsOfGroup(R),g->List(pg,x->bits(x^g)));bases:=List(es,E->List(GeneratorsOfGroup(E),bits));
   Add(witnesses,[i,N,GeneratorsOfGroup(H),List(GeneratorsOfGroup(H),x->Image(rho,x)),repscos,GeneratorsOfGroup(R),pg]);Add(data,[i,Size(T),Size(R0),Size(N),z,ceiling,mu,mats,bases]);Add(rows,[i,labels[i],Size(T),Size(H),Size(R0),Size(N),Length(ns),z,ceiling,Length(es),mu]);
   Print("STRUCTURAL FRAME ",Last(rows),"\n");
  od;
 od;
 Check(frames=30,"all thirty literal stabilizer-kernel frames retained");
 PrintTo("frames8.json",data,"\n");
 PrintTo("bindings8.g","FrameEightTops:=List(",List(tops,GeneratorsOfGroup),",Group);;\nFrameEightBindings:=",witnesses,";;\n");
 Print("PRIMITIVE INPUT ROWS ",primrows,"\n");Print("PASS EIGHT-FRAME PRODUCER ",checks," assertions; ",frames," frames; all mu<=2, all z2*(T)<=2; exported every invariant module for independent closure\n");
end;;Run();QUIT;
