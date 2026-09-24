# Standalone catalogue-free, subgroup-first common-source second-moment check.
# Run: gap -q -T computations/gap/verify_shared_source_moment.g
SizeScreen([240,1000000]);;
VerifySharedSourceMoment:=function()
 local checks,ck,R,N,phi,Q,eps,source,DP,pp,ee,CP,cp,ce,gens,images,map,
       S,J,F,j,fibre,recovered,pairs,fullPairs,good,expected,records,projection;
 checks:=0;
 ck:=function(ok,msg)
   checks:=checks+1;
   if not ok then Print("FAIL shared source: ",msg,"\n");QUIT_GAP(1);fi;
 end;
 R:=Group((1,2)(3,4),(1,2,3));N:=DerivedSubgroup(R);
 phi:=NaturalHomomorphismByNormalSubgroup(R,N);Q:=Image(phi);
 ck(Size(R)=12 and Size(N)=4 and IsElementaryAbelian(N) and Size(Q)=3,"literal A4-to-C3 cover");
 eps:=function(A,B)
   local total,L;
   total:=0;
   for L in NormalSubgroups(A) do
     if Size(A)/Size(L)=Size(B) and IsomorphismGroups(FactorGroup(A,L),B)<>fail then
       total:=total+Size(AutomorphismGroup(B));
     fi;
   od;
   return total;
 end;
 records:=[];
 for source in [Group((1,2,3)),Group((1,2,3),(4,5,6))] do
   DP:=DirectProduct(Q,Q,source);pp:=List([1..3],i->Projection(DP,i));ee:=List([1..3],i->Embedding(DP,i));
   CP:=DirectProduct(R,R,source);cp:=List([1..3],i->Projection(CP,i));ce:=List([1..3],i->Embedding(CP,i));
   gens:=GeneratorsOfGroup(CP);
   images:=List(gens,x->Image(ee[1],Image(phi,Image(cp[1],x)))*Image(ee[2],Image(phi,Image(cp[2],x)))*Image(ee[3],Image(cp[3],x)));
   map:=GroupHomomorphismByImages(CP,DP,gens,images);
   ck(map<>fail and IsSurjective(map),"joint cover homomorphism");
   good:=0;pairs:=0;fullPairs:=0;
   # Enumerate subgroups FIRST. The graph and onto properties are filters,
   # not assumptions that the two quotient coordinates are independent.
   for S in AllSubgroups(DP) do
     J:=Image(pp[3],S);
     if Size(S)<>Size(J) or Image(pp[1],S)<>Q or Image(pp[2],S)<>Q then continue;fi;
     good:=good+1;F:=PreImage(map,S);
     ck(Size(F)=16*Size(J),"all lifts of the two nontrivial cover kernels");
     ck(Image(cp[1],F)=R and Image(cp[2],F)=R and Image(cp[3],F)=J,"all three actual projections retained");
     ck(Image(map,F)=S,"whole graph relation recovered");
     for j in Elements(J) do
       fibre:=Filtered(Elements(F),x->Image(cp[3],x)=j);
       recovered:=Set(List(fibre,x->[Image(phi,Image(cp[1],x)),Image(phi,Image(cp[2],x))]));
       ck(Length(fibre)=16 and Length(recovered)=1,"same-source ordered map pair recovered from every fibre");
     od;
     if J=source then
       pairs:=pairs+1;
       projection:=Group(List(GeneratorsOfGroup(S),x->Image(ee[1],Image(pp[1],x))*Image(ee[2],Image(pp[2],x))));
       if Size(projection)=9 then fullPairs:=fullPairs+1;fi;
     fi;
   od;
   expected:=Sum(AllSubgroups(source),J->eps(J,Q)^2);
   ck(good=expected,"subgroup-first total equals SAME-source squared epimorphism count");
   Add(records,[eps(source,Q),pairs,fullPairs,good]);
 od;
 ck(records=[[2,4,0,4],[8,64,48,80]],"exact shared-C3 and C3-squared moment records");
 Print("SHARED_SOURCE_RECORDS ",records,"\n");
 Print("PASS SHARED SOURCE: ",checks," assertions; proper joint images retained\n");
end;;
VerifySharedSourceMoment();
QUIT_GAP(0);
