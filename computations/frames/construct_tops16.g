# Complete two-frame invariant-kernel and quotient-complement construction.
SizeScreen([240,50]);;
Run:=function()
 local checks,Check,S4,tops,alltops,H,T,G,g,h,c,types,hom,hs,R0,
       topRows,gens,imgs,onto,which,cosets,reps,induced,R,Rinv,M,W,E,
       lift,blocks,trans,frames,frame,es,cursor,F,closureCells,pc,fp,
       fg,rels,rg,phi,Q,Mb,d,top,cs,columns,j,k,col,values,rel,x,
       rankZ,zdim,fixdim,h1dim,a,b,C,U,classes,classrows,certs,
       pos,normalizer,old,rows,interfaces,actualcells,nonsplit,
       P,invhom,flip,orig,actionid,normals;
 checks:=0;closureCells:=0;interfaces:=0;actualcells:=0;
 Check:=function(ok,msg)if not ok then Error(msg);fi;checks:=checks+1;end;
 S4:=SymmetricGroup(4);alltops:=List(ConjugacyClassesSubgroups(S4),Representative);
 Check(Length(alltops)=11 and ForAny(alltops,H->Size(H)=1),"eleven candidate S4 subgroup classes include the trivial group");
 for a in [1..Length(alltops)] do
  for b in [a+1..Length(alltops)] do Check(not IsConjugate(S4,alltops[a],alltops[b]),"candidate top classes are distinct");od;
  H:=alltops[a];for g in Elements(S4) do F:=ClosureGroup(H,g);Check(ForAny(alltops,G->Size(G)=Size(F) and IsConjugate(S4,G,F)),"closure under adjoining every S4 element proves subgroup completeness");od;
 od;
 tops:=Filtered(alltops,T->IsTransitive(T,[1..4]));Check(Length(tops)=5,"complete five transitive four-point tops");topRows:=[];
 for T in tops do H:=Stabilizer(T,1);rows:=[];
  for R0 in [Group((1,2,3)),Group((1,2,3),(1,2))] do
   onto:=Filtered(AllHomomorphisms(H,R0),hom->Size(Image(hom))=Size(R0));Add(rows,Length(onto));
   Check((Length(onto)>0)=(Size(T)=4*Size(R0)),"only A4/C3 and S4/S3 stabilizer epimorphisms survive");
  od;Add(topRows,[Size(T),StructureDescription(T),Size(H),rows]);
 od;
 frames:=[];
 lift:=function(g,i)local p,j;p:=[1..16];for j in [1..4] do p[4*i+j]:=4*i+j^g;od;return PermList(p);end;
 M:=Group(Concatenation(List([0..3],i->[(lift((1,2)(3,4),i)),(lift((1,3)(2,4),i))])));blocks:=List([0..3],i->[4*i+1..4*i+4]);
 for which in [1,2] do
  if which=1 then T:=AlternatingGroup(4);else T:=S4;fi;H:=Stabilizer(T,4);R0:=H;
  cosets:=RightCosets(T,H);reps:=List(cosets,Representative);
  hom:=IdentityMapping(H);
  induced:=function(g)local p,i,j,h,k;p:=[1..16];for i in [1..4] do j:=Position(cosets,cosets[i]*g);h:=reps[i]*g*reps[j]^-1;for k in [1..4] do p[4*(i-1)+k]:=4*(j-1)+k^Image(hom,h);od;od;return PermList(p);end;
  R:=Group(List(GeneratorsOfGroup(T),induced));
  Check(Size(R)=Size(T) and Size(Kernel(ActionHomomorphism(R,blocks,OnSets)))=1,"induced linear frame has faithful four-block top and no block kernel");
  Check(Size(Action(Stabilizer(R,blocks[1],OnSets),blocks[1]))=Size(R0),"induced frame has exact required local linear image");
  if which=1 then
   hs:=GeneratorsOfGroup(H);hom:=GroupHomomorphismByImages(H,H,hs,List(hs,h->h^-1));Rinv:=Group(List(GeneratorsOfGroup(T),induced));flip:=Product(List([0..3],i->lift((1,2),i)));
   Check(R^flip=Rinv and M^flip=M,"both C3 orientations are fused by one actual ambient Frobenius conjugation");
  else
   onto:=Filtered(AllHomomorphisms(H,H),hom->Size(Image(hom))=6);
   Check(Length(onto)=6 and ForAll(onto,hom->ForAny(Elements(H),g->ForAll(GeneratorsOfGroup(H),h->Image(hom,h)=h^g))),"all six S3 epimorphisms are inner");
  fi;
  Add(frames,[which,R,ClosureGroup(M,R)]);
 od;
 classes:=[];classrows:=[];certs:=[];rows:=[];
 for frame in frames do
  which:=frame[1];R:=frame[2];W:=frame[3];rg:=GeneratorsOfGroup(R);
  es:=[TrivialSubgroup(M)];cursor:=1;
  while cursor<=Length(es) do
   E:=es[cursor];
   for g in RightTransversal(M,E) do
    if g in E then continue;fi;
    F:=NormalClosure(W,ClosureGroup(E,g));closureCells:=closureCells+1;
    if not F in es then Add(es,F);fi;
   od;cursor:=cursor+1;
  od;
  SortBy(es,Size);
  normals:=Filtered(NormalSubgroups(W),E->IsSubgroup(M,E));
  Check(Set(es)=Set(normals),"constructive cyclic-submodule closure equals all normal binary kernels");
  fp:=Image(IsomorphismFpGroupByGenerators(R,rg));fg:=FreeGeneratorsOfFpGroup(fp);rels:=RelatorsOfFpGroup(fp);
  Check(Size(fp)=Size(R) and Length(fg)=Length(rg),"exact presentation on the actual frame generators");
  orig:=[];
  for E in es do
   phi:=NaturalHomomorphismByNormalSubgroup(W,E);Q:=Image(phi);Mb:=Image(phi,M);pc:=Pcgs(Mb);d:=Length(pc);top:=List(rg,g->Image(phi,g));
   if d=0 then cs:=[Q];else cs:=ComplementClassesRepresentatives(Q,Mb);fi;
   columns:=[];
   for j in [1..Length(rg)] do for k in [1..d] do
    values:=ShallowCopy(top);values[j]:=pc[k]*values[j];col:=[];
    for rel in rels do x:=MappedWord(rel,fg,values);Check(x in Mb,"all perturbed relators remain in the same binary quotient module");Append(col,ExponentsOfPcElement(pc,x));od;
    Add(columns,List(col,x->x*One(GF(2))));
   od;od;
   if Length(columns)=0 or Length(columns[1])=0 then rankZ:=0;else rankZ:=RankMat(columns);fi;
   zdim:=Length(rg)*d-rankZ;fixdim:=LogInt(Size(Centralizer(Mb,Group(top))),2);h1dim:=zdim-d+fixdim;
   Check(h1dim>=0 and Length(cs)=2^h1dim,"all complement classes accounted for by exact Z1/B1 dimension");
   for a in [1..Length(cs)] do for b in [a+1..Length(cs)] do Check(not IsConjugate(Q,cs[a],cs[b]),"complement representatives occupy distinct translation-conjugacy classes");od;od;
   interfaces:=interfaces+1;
   for C in cs do
    Check(Size(C)*Size(Mb)=Size(Q) and Size(Intersection(C,Mb))=1,"literal full complement in W/E");U:=PreImage(phi,C);
    Check(Intersection(U,M)=E and Size(U)/Size(E)=Size(R),"preimage recovers exact translation kernel and full original top");
    if Size(E)=1 then Check(not IsTransitive(U,[1..16]),"zero translation base cannot supply the exact transitive local action");continue;fi;
    Check(IsTransitive(U,[1..16]) and Size(Action(Stabilizer(U,blocks[1],OnSets),blocks[1]))=4*Size(Stabilizer(R,blocks[1],OnSets)),"nonzero invariant base gives actual transitivity and exact local A4/S4");
    pos:=First([1..Length(classes)],i->Size(classes[i])=Size(U) and IsConjugate(SymmetricGroup(16),classes[i],U));
    if pos=fail then
     Add(classes,U);pos:=Length(classes);normalizer:=Size(Normalizer(SymmetricGroup(16),U));nonsplit:=Length(ComplementClassesRepresentatives(U,E))=0;
     Add(classrows,[pos,which,Size(U),Size(E),normalizer,nonsplit]);
    fi;
    Add(certs,[which,E,U,pos,Length(ComplementClassesRepresentatives(U,E))=0]);actualcells:=actualcells+1;
   od;
   Add(orig,[Size(E),d,zdim,fixdim,h1dim,Length(cs)]);
  od;
  Add(rows,[which,Size(R),Length(es),orig]);Print("DONE FRAME ",which," kernels ",Length(es)," total actual certificates ",Length(certs)," classes ",Length(classes),"\n");
 od;
 PrintTo("tops16_generated.g","# Generated literal actions and certificates; source construction is the completeness proof.\nAffineFourDZeroClasses:=",classes,";;\nAffineFourDZeroRows:=",classrows,";;\nAffineFourDZeroCertificates:=",certs,";;\n");
 Print("TOP MAP ROWS ",topRows,"\nFULL INTERFACE ROWS ",rows,"\nACTUAL CLASS ROWS ",classrows,"\n");
 Print("PASS FOUR-BLOCK CONSTRUCTION ",checks," assertions; ",closureCells," constructive kernel-closure cells; ",interfaces," module/complement interfaces; ",Length(certs)," actual certificates; ",Length(classes)," S16 classes\n");
end;;
Run();
QUIT;
