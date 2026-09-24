# Complete constructive classification on four binary blocks with A4/S4 top.
FBCheck:=FCRequire;;
FBRows:=FCPerms;;
FBGroup:=FEWGroup;;
FBTargets:=function()
 local V,a,t,s;
 V:=Group((1,2)(3,4),(1,3)(2,4),(5,6)(7,8),(5,7)(6,8));
 a:=(1,2,3)(5,6,7);t:=(1,2)(5,6);s:=(1,5)(2,6)(3,7)(4,8);
 return List([[a],[a,s],[a,t*s],[a,t,s]],gs->Group(Concatenation(GeneratorsOfGroup(V),gs)));
end;;
FBClassify:=function()
 local f,M,C,A,gens,Es,spaces,E,H,g,i,j,k,top,T,W,inv,gs,x,y,U,reps,actual,profile;
 f:=[(1,2),(3,4),(5,6),(7,8)];M:=Group(f);C:=Group(Product(f));
 A:=Group(f[1]*f[2],f[2]*f[3],f[3]*f[4]);Es:=[Group(()),C,A,M];
 gens:=[[(1,3,5)(2,4,6),(1,3)(2,4)(5,7)(6,8)],[(1,3,5,7)(2,4,6,8),(1,3)(2,4)]];
 # Adjoining every vector, with no subgroup-library coverage premise.
 spaces:=[TrivialSubgroup(M)];i:=1;
 while i<=Length(spaces) do
  for g in Elements(M) do H:=ClosureGroup(spaces[i],g);if not H in spaces then Add(spaces,H);fi;od;
  i:=i+1;
 od;
 FBCheck(Length(spaces)=67,"all subspaces of the four-dimensional binary base");
 actual:=[];profile:=[];
 for j in [1..2] do
  top:=gens[j];T:=Group(top);W:=Group(Concatenation(f,top));
  inv:=Filtered(spaces,E->IsNormal(W,E));FBCheck(Set(inv)=Set(Es),"exact invariant-subspace list");
  for k in [1..4] do
   E:=Es[k];gs:=[];
   for x in Elements(M) do for y in Elements(M) do
    U:=Group(Concatenation(GeneratorsOfGroup(E),[x*top[1],y*top[2]]));
    if Intersection(U,M)=E and not U in gs then Add(gs,U);fi;
   od;od;
   reps:=[];for U in gs do if ForAll(reps,H->not IsConjugate(M,U,H)) then Add(reps,U);fi;od;
   Add(profile,[Size(T),Size(E),Length(gs),Length(reps),Number(reps,U->IsTransitive(U,[1..8]))]);
   for U in reps do if IsTransitive(U,[1..8]) then
    FBCheck(Size(U)=Size(E)*Size(T),"entire top with exact block kernel");Add(actual,U);
   fi;od;
  od;
 od;
 FBCheck(profile=[[12,1,8,1,0],[12,2,16,2,2],[12,8,1,1,1],[12,16,1,1,1],
   [24,1,16,2,1],[24,2,16,2,2],[24,8,2,2,2],[24,16,1,1,1]],"complete lift and graph profile");
 FBCheck(Length(actual)=10,"ten transitive physical classes");
 for i in [1..10] do for j in [i+1..10] do FBCheck(not IsConjugate(SymmetricGroup(8),actual[i],actual[j]),"different physical classes");od;od;
 return rec(actions:=actual,profile:=profile,M:=M,C:=C);
end;;

# Every normal is an intersection of irreducible kernels: apply the regular
# representation of U/N. Closure below therefore reconstructs the full lattice.
FBNormals:=function(U)
 local chars,kernels,normals,i,K,N,H;
 chars:=Irr(U);kernels:=Set(List(chars,KernelOfCharacter));normals:=[U];i:=1;
 while i<=Length(normals) do
  for K in kernels do N:=Intersection(normals[i],K);if not N in normals then Add(normals,N);fi;od;
  i:=i+1;
 od;
 return rec(normals:=normals,chars:=chars);
end;;
FBMenu:=function(U,produce,entry,C,targets)
 local ctx,normals,charrows,chi,i,k,N,large,phi,Q,target,iso,map,normal,out;
 ctx:=FBNormals(U);
 if produce then normals:=ctx.normals;
 else
  normals:=List(entry.normals,n->FBGroup(n.generators,8));
  FBCheck(Length(Set(normals))=Length(normals) and Set(normals)=Set(ctx.normals),"complete literal normal lattice");
  FBCheck(List(normals,Size)=List(entry.normals,n->n.order),"normal orders");
 fi;
 charrows:=[];for chi in ctx.chars do
  k:=Position(normals,KernelOfCharacter(chi));FBCheck(k<>fail,"character kernel belongs to complete normal lattice");AddSet(charrows,[k,chi[1]]);
 od;
 large:=Size(Intersection(U,Group((1,2),(3,4),(5,6),(7,8))))>=8;
 if produce then
  out:=rec(generators:=FBRows(GeneratorsOfGroup(U),8),order:=Size(U),
    normalizer_order:=Size(Normalizer(SymmetricGroup(8),U)),
    normals:=List(normals,N->rec(generators:=FBRows(SmallGeneratingSet(N),8),order:=Size(N))),
    character_kernels:=charrows,large_kernel:=large,target:=0,images:=[]);
 else
  out:=entry;FBCheck(entry.order=Size(U) and entry.normalizer_order=Size(Normalizer(SymmetricGroup(8),U)),"original action order and normalizer");
  FBCheck(entry.character_kernels=charrows and entry.large_kernel=large,"actual irreducible kernels, degrees and large-kernel role");
 fi;
 if large then
  FBCheck(IsSubgroup(U,C) and Centralizer(U,C)=U,"constant central C2 retained");
  FBCheck(ForAll(normals,N->Size(N)=1 or IsSubgroup(N,C)),"every nontrivial normal contains C");
  FBCheck(ForAny(ctx.chars,chi->Size(KernelOfCharacter(chi))=1),"faithful irreducible on original action");
  if produce then
   phi:=NaturalHomomorphismByNormalSubgroup(U,C);Q:=Image(phi);
   target:=First([1..4],i->Size(Q)=Size(targets[i]) and IsomorphismGroups(Q,targets[i])<>fail);
   FBCheck(target<>fail,"fixed central quotient target");iso:=IsomorphismGroups(Q,targets[target]);
   out.target:=target;out.images:=FBRows(List(GeneratorsOfGroup(U),g->Image(iso,Image(phi,g))),8);
  else
   FBCheck(out.target in [1..4],"target index");Q:=targets[out.target];
   map:=GroupHomomorphismByImages(U,Q,GeneratorsOfGroup(U),FEWPerms(out.images,8));
   FBCheck(map<>fail and Image(map)=Q and Kernel(map)=C,"literal original-source quotient map");
   FBCheck(Length(normals)=1+Length(FBNormals(Q).normals),"all nontrivial normal preimages retained");
  fi;
 else FBCheck(out.target=0 and out.images=[],"no spurious large-kernel target");fi;
 return out;
end;;
FBRun:=function(produce,data)
 local classification,targets,actions,U,i,j,out,menus,total,Q,qn,lines;
 classification:=FBClassify();targets:=FBTargets();menus:=[];total:=0;
 if produce then actions:=classification.actions;
 else
  FBCheck(data.schema_version=1 and data.profile=classification.profile,"schema and complete lift profile");
  actions:=List(data.actions,a->FBGroup(a.generators,8));
  FBCheck(Length(actions)=10,"all ten actions retained");
  for i in [1..10] do
   FBCheck(IsConjugate(SymmetricGroup(8),actions[i],classification.actions[i]),"constructive class-to-data correspondence");
   FBCheck(IsSubgroup(Group((1,2),(3,4),(5,6),(7,8),(1,3,5,7)(2,4,6,8),(1,3)(2,4)),actions[i]),"literal original block action");
  od;
 fi;
 for i in [1..10] do
  if produce then out:=FBMenu(actions[i],true,fail,classification.C,targets);
  else out:=FBMenu(actions[i],false,data.actions[i],classification.C,targets);fi;
  Add(menus,out);total:=total+Length(out.normals);
 od;
 FBCheck(Number(menus,a->a.large_kernel)=5,"five large-kernel actions");
 FBCheck(List(menus,a->a.normalizer_order)=[48,48,384,384,48,48,48,384,384,384],"complete physical weight profile");
 Q:=targets[1];qn:=FBNormals(Q);lines:=Filtered(qn.normals,N->Size(N)=4);
 FBCheck(Length(lines)=5 and ForAll(lines,N->IsomorphismGroups(Q/N,AlternatingGroup(4))<>fail),"five distinct A4 quotient lines");
 FBCheck(ForAll(qn.normals,N->Size(N) in [1,4,16,48]),"complete repeated-F4 quotient menu");
 FBCheck(ForAll(qn.chars,chi->Size(KernelOfCharacter(chi))>1),"repeated-F4 quotient has no faithful irreducible");
 if produce then FCEmit(rec(schema_version:=1,profile:=classification.profile,actions:=menus,normal_count:=total));
 else FBCheck(data.normal_count=total,"complete normal count");fi;
 Print("PASS FOUR BLOCK ",String(produce),": 10 actions / ",total," normals / 5 central quotient maps\n");
end;;
