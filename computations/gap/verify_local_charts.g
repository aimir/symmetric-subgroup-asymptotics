# Run through run_local_checks.py, which supplies parsed literal JSON records.
# No transitive/SmallGroup catalogue is used unless CheckCatalogueLocators=true.
SizeScreen([240,1000000]);;
VerifyLocalCharts:=function(d16,d8,locators)
 local checks,ck,perms,makeMap,correlated,sg,ig,kg,U,P,N,phi,orbs,images,
       normal4,C2,old,new,oe,ne,gens,ims,g,H,Hnew,transport,V,vg,entry,Q,
       alpha,beta,coverKernel,normal2,i,sourceGroups;
 checks:=0;
 ck:=function(ok,msg)
   checks:=checks+1;
   if not ok then Print("FAIL local charts: ",msg,"\n");QUIT_GAP(1);fi;
 end;
 perms:=rows->List(rows,PermList);
 makeMap:=function(A,B,ag,bg)
   local f;
   ck(Length(ag)=Length(bg),"one map image per source generator");
   f:=GroupHomomorphismByImages(A,B,ag,bg);
   ck(f<>fail and IsGroupHomomorphism(f) and IsSurjective(f),"literal onto homomorphism");
   return f;
 end;
 # Use actual fibre products, including every automorphism of the common Q.
 correlated:=function(A,B,Q,a,b,axis)
   local src,dst,qq,sm,tm,gs,is,x,sigma,relation,X,Y,autos;
   src:=DirectProduct(A,Q);dst:=DirectProduct(B,Q);qq:=DirectProduct(Q,Q);
   gs:=GeneratorsOfGroup(src);
   is:=List(gs,x->Image(Embedding(qq,1),Image(a,Image(Projection(src,1),x)))*Image(Embedding(qq,2),Image(Projection(src,2),x)));
   sm:=makeMap(src,qq,gs,is);
   gs:=GeneratorsOfGroup(dst);
   is:=List(gs,x->Image(Embedding(qq,1),Image(b,Image(Projection(dst,1),x)))*Image(Embedding(qq,2),Image(Projection(dst,2),x)));
   tm:=makeMap(dst,qq,gs,is);
   autos:=Elements(AutomorphismGroup(Q));
   ck(Length(autos)=32,"all32 quotient automorphisms in each width8 regression");
   for sigma in autos do
     relation:=Group(List(GeneratorsOfGroup(Q),x->Image(Embedding(qq,1),x)*Image(Embedding(qq,2),Image(sigma,x))));
     X:=PreImage(sm,relation);Y:=PreImage(tm,relation);
     ck(Intersection(X,Image(Embedding(src,1)))=Image(Embedding(src,1),axis),"exact original Goursat axis");
     ck(Image(Projection(src,1),X)=A and Image(Projection(dst,1),Y)=B,"full original and replacement projections");
     ck(Image(sm,X)=relation and Image(tm,Y)=relation,"same whole correlated quotient relation");
     ck(PreImage(sm,Image(tm,Y))=X and PreImage(tm,Image(sm,X))=Y,"both full-preimage inverses");
   od;
 end;
 ck(d16.degree=16 and d16.source_order=1024 and d16.kernel_order=4 and d16.image_order=256,"degree16 metadata");
 ck(d16.target_orbit_types=["C4 regular","D8 natural","D8 natural","D8 natural"],"degree16 ordered orbit metadata");
 sg:=perms(d16.source_generators);ig:=perms(d16.image_generators);kg:=perms(d16.kernel_generators);
 U:=Group(sg);P:=Group(ig);N:=Group(kg);phi:=makeMap(U,P,sg,ig);
 ck(Kernel(phi)=N and Size(U)=1024 and Size(P)=256 and Size(N)=4,"degree16 exact orders and literal kernel");
 ck(IsTransitive(U,[1..16]) and NrMovedPoints(U)=16,"degree16 transitive source");
 normal4:=Filtered(NormalSubgroups(U),x->Size(x)=4);
 ck(Length(normal4)=1 and normal4[1]=N,"unique literal normal order4 axis");
 ck(Size(Centre(P))=16 and IsElementaryAbelian(Centre(P)),"degree16 whole central socle");
 ck(FrattiniSubgroup(P)=Centre(P) and Size(DerivedSubgroup(P))=8,"degree16 Frattini and derived subgroups");
 ck(Exponent(P)=4 and NilpotencyClassOfGroup(P)=2,"degree16 class and exponent");
 orbs:=Set(List(Orbits(P,[1..16]),Set));
 ck(orbs=List([0..3],i->[4*i+1..4*i+4]),"literal four target orbits");
 images:=List(orbs,o->Image(ActionHomomorphism(P,o)));
 ck(List(images,Size)=[4,8,8,8],"full projection orders");
 ck(IsCyclic(images[1]) and ForAll(images{[2..4]},x->IsomorphismGroups(x,DihedralGroup(8))<>fail),"C4,D8,D8,D8 target types");
 ck(Size(P)<Product(List(images,Size)),"proper subdirect target retained, not full product");
 # A correlated exterior P x C2 remains attached throughout this control.
 C2:=Group((1,2));old:=DirectProduct(U,P,C2);new:=DirectProduct(P,P,C2);
 oe:=List([1..3],i->Embedding(old,i));ne:=List([1..3],i->Embedding(new,i));
 gens:=GeneratorsOfGroup(old);
 ims:=List(gens,g->Image(ne[1],Image(phi,Image(Projection(old,1),g)))*Image(ne[2],Image(Projection(old,2),g))*Image(ne[3],Image(Projection(old,3),g)));
 transport:=makeMap(old,new,gens,ims);
 H:=Group(Concatenation(List([1..Length(sg)],i->Image(oe[1],sg[i])*Image(oe[2],ig[i])),[Image(oe[3],C2.1)]));
 Hnew:=Image(transport,H);
 ck(Intersection(H,Image(oe[1]))=Image(oe[1],N),"degree16 exact source axis with correlated exterior");
 ck(PreImage(transport,Hnew)=H and Size(H)=2048 and Size(Hnew)=512,"degree16 whole inverse and correlated group orders");
 ck(Image(Projection(new,1),Hnew)=P and Image(Projection(new,2),Hnew)=P and Image(Projection(new,3),Hnew)=C2,"all correlated replacement and exterior projections");
 ck(SortedList(List(Orbits(Hnew,[1..34]),Length))=[2,4,4,4,4,4,4,4,4],"correlated physical orbit word");
 if locators then
   ck(TransitiveIdentification(U)=1086 and IdGroup(P)=[256,7667],"OPTIONAL degree16 catalogue locators");
 fi;
 Print("PASS DEGREE16: literal chart and correlated proper-subdirect inverse\n");
 ck(d8.schema_version=1 and d8.degree=8 and Length(d8.charts)=3,"degree8 schema and chart count");
 vg:=perms(d8.cover_generators);V:=Group(vg);
 ck(Size(V)=64 and IsTransitive(V,[1..8]) and NrMovedPoints(V)=8,"literal degree8 replacement carrier");
 if locators then ck(TransitiveIdentification(V)=27,"OPTIONAL degree8 carrier locator");fi;
 sourceGroups:=[];
 for i in [1..3] do
   entry:=d8.charts[i];sg:=perms(entry.source_generators);U:=Group(sg);N:=Group(perms(entry.kernel_generators));
   ck(ForAll(sourceGroups,x->not IsConjugate(SymmetricGroup(8),x,U)),"three distinct degree8 permutation action classes");
   Add(sourceGroups,U);
   Q:=Group(perms(entry.quotient_generators));
   ck(entry.quotient_degree=16 and Size(Q)=16 and IsTransitive(Q,[1..16]),"auxiliary regular quotient representation");
   ck(entry.source_order=32 and entry.kernel_order=2 and entry.cover_order=64 and entry.quotient_order=16,"degree8 order metadata");
   alpha:=makeMap(U,Q,sg,perms(entry.alpha_images));beta:=makeMap(V,Q,vg,perms(entry.beta_images));
   coverKernel:=Group(perms(entry.cover_kernel_generators));
   ck(Size(U)=32 and Size(N)=2 and Kernel(alpha)=N,"degree8 exact source quotient kernel");
   ck(Kernel(beta)=coverKernel and Size(coverKernel)=4,"degree8 exact replacement kernel");
   ck(IsTransitive(U,[1..8]) and NrMovedPoints(U)=8,"same physical degree8");
   normal2:=Filtered(NormalSubgroups(U),x->Size(x)=2);
   ck(Length(normal2)=1 and normal2[1]=N,"unique literal normal order2 axis");
   correlated(U,V,Q,alpha,beta,N);
   if locators then ck(TransitiveIdentification(U)=[16,20,21][i] and IdGroup(Q)=[16,3],"OPTIONAL degree8 source/quotient locators");fi;
   Print("PASS DEGREE8 CHART ",i,": literal quotient and32 correlated full-preimage inverses\n");
 od;
 Print("PASS LOCAL CHARTS: ",checks," assertions; four literal charts;97 correlated controls\n");
 if locators then Print("PASS OPTIONAL CATALOGUE LOCATORS\n");fi;
end;;
VerifyLocalCharts(Degree16Data,Degree8Data,CheckCatalogueLocators);
