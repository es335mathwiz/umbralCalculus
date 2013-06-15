(* Mathematica Package *)

(* Created by the Wolfram Workbench Jun 15, 2013 *)

BeginPackage["umbralCalculus`",{"Combinatorica`"}]

(* Exported symbols added here with SymbolName::usage *) 

(* Implementation of the package *)


(* Mathematica Package *)

(*
classical umbral calculus   
nardo and senato umbral nature of poisson random variables
*)

(*
umbra a function of positive integers and an alphabet
umbra[Function[],alphabet]
*)

(* Created by the Wolfram Workbench Sep 7, 2012 *)

getFunction::usage = "getFunction  "

getAlphabet::usage = "getAlphabet  "

ee::usage = "ee  "

$augmentation::usage = "$augmentation  "

gf::usage = "gf  "

umbra::usage = "umbra  "

$unity::usage = "$unity  "

$singleton::usage = "$singleton  "

$bernoulli::usage = "$bernoulli  "

$bell::usage = "$bell  "

$booleanUnity::usage = "$booleanUnity  "

getArg::usage = "getArg  "

dotPower::usage = "dotPower  "

lambdaFactorial::usage = "lambdaFactorial  "

mLambdaFactorial::usage = "mLambdaFactorial  "

termFactor::usage = "termFactor  "

termDotPows::usage = "termDotPows  "

makeSimilar::usage = "makeSimilar  "

prepTerm::usage = "prepTerm  "

cmpMultiplicities::usage = "cmpMultiplicities  "

uniFa::usage = "uniFa  "

minusOne::usage = "minusOne  "

dotProduct::usage = "dotProduct  "

powsOfnnDotGamma::usage = "powsOfnnDotGamma  "

getAllArgs::usage = "getAllArgs  "

alphaFactorial::usage = "alphaFactorial  "

powsOfDotProduct::usage = "powsOfDotProduct  "

ff::usage = "ff  "

makeMultSubs::usage = "makeMultSubs  "

allSubdivisions::usage = "allSubdivisions  "

kFori::usage = "kFori  "

newkFori::usage = "newkFori  "

MFB::usage = "MFB  "

$ff::usage = "$ff  "

$gg::usage = "$gg  "

hardyDoubleFac::usage = "hardyDoubleFac  "

multiplicity::usage = "multiplicity  "

joint::usage = "joint  "

UMFB::usage = "UMFB  "

applyFaDiBruno::usage = "applyFaDiBruno[order_Integer,gArgs_Integer,outerFuncs_List,innerFuncs_List]"

lambdaFacetDiffOrder::usage = "lambdaFacetDiffOrder  "
(* Exported symbols added here with SymbolName::usage *) 

Begin["`Private`"]
(* Implementation of the package *)


theIndex[beta_List]:=index[beta];(*for export*)


index[beta_List]:=
index/:index[beta]=(*memoized*)
With[{nn=Length[beta]},
Sum[With[{sc=(Apply[Plus , Drop[beta,cc-1]])-1},
pascal[nn-cc+1,sc]],{cc,nn}]]

pascal[cc_Integer,kk_Integer]:=
pascal/:pascal[cc,kk]=(*memoized*)
	    If[kk==-1, 0,If[cc==0||kk==0,1,
	      Binomial[cc+kk,kk]]]
getFunction[umbra[ff_Function,alphabet_List]]:=ff
getAlphabet[umbra[ff_Function,alphabet_List]]:=alphabet

Unprotect[$augmentation,$unity,$singleton,$bernoulli,$bell,$booleanUnity,Power]
Power[0,0]=1;
$augmentation=With[{arg=Unique["umbraArg"]},
umbra[Function @@ {arg,KroneckerDelta[0,arg]},{}]];
gf[$augmentation,zz_]:=1;


$unity=With[{arg=Unique["umbraArg"]},
umbra[Function @@ {arg,1},{}]]
gf[$unity,zz_]:=E^zz

$singleton=With[{arg=Unique["umbraArg"]},
umbra[Function @@ {arg,KroneckerDelta[1,arg]},{}]]
gf[$singleton,zz_]:=1+zz

$bernoulli=With[{arg=Unique["umbraArg"]},
umbra[Function @@{arg,BernoulliB[arg]},{}]]
gf[$bernoulli,zz_]:=zz/(E^zz-1)

$bell=With[{arg=Unique["umbraArg"]},
umbra[Function @@ {arg,BellB[arg]},{}]]
gf[$bell,zz_]:=E^(E^zz-1)

$booleanUnity=With[{arg=Unique["umbraArg"]},
umbra[Function @@ {arg,arg!},{}]]
gf[$booleanUnity,zz_]:=1/(1-zz)

Protect[$augmentation,$unity,$singleton,$bernoulli,$bell,$booleanUnity]
SetAttributes[ee,Append[Attributes[ee],Listable]]
ee[(uVal_umbra)^nn_Integer]:=getFunction[uVal][nn]
ee[nn_Integer]:=nn
ee[uVal_umbra]:=getFunction[uVal][1]

getArg[uVal_umbra]:=getFunction[uVal][[1]]

dotPower[uVal_,1]:=uVal
dotPower[anUmbra_,nn_Integer]:=With[{theSims=Table[makeSimilar[anUmbra],{nn}]},Times @@ theSims]
getAllArgs[xx_]:=Union[Cases[xx,HoldPattern[Function[yy_,zz___]]->yy,Infinity]]

(*$IterationLimit=$RecursionLimit=Infinity;*)
ee[Plus[xx_,yy__]]:=ee[xx]+ee[Plus[yy]]
ee[xx_]:=ee[Expand[xx]]
ee[Times[xx_,yy__]]:=Times[xx,ee[Times[yy]]]/;FreeQ[xx,umbra]
ee[Times[xx_umbra,yy__]]:=Times[ee[xx],ee[Times[yy]]]
ee[Times[xx_umbra^thePow_Integer,yy__]]:=Times[ee[xx^thePow],ee[Times[yy]]]





dotProduct[nn_Integer,uVal_umbra]:=
With[{sims=Table[makeSimilar[uVal],{nn}]},
	Plus @@ sims]/;nn>=0

dotProduct[nn_Integer,uVal_umbra]:=
With[{sims=Table[makeSimilar[uVal],{-nn}]},
	-1*(Plus @@ sims)]/;nn<0
		


gf[uVal_umbra,nn_Integer]:=
If[nn==0,1,ee[uVal^nn]  * getArg[uVal]^nn/Factorial[nn]]


lambdaFactorial[multiplicities_List]:=
With[{forProd=Factorial/@Range[Length[multiplicities]]},
Times @@(forProd^multiplicities)]

mLambdaFactorial[multiplicities_List]:=
Times @@(Factorial/@multiplicities)


termFactor[nn_Integer,multiplicities_List]:=
With[{facPart=dotProduct[nn,$singleton]^(Plus @@multiplicities)/
(mLambdaFactorial[multiplicities]*
lambdaFactorial[multiplicities])},
facPart]

powsOfnnDotGamma[nn_Integer,gamma_umbra,ii_Integer]:=
With[{pttns=cmpMultiplicities/@IntegerPartitions[ii]},
Plus @@	((Factorial[ii]*prepTerm[nn,gamma,#,ii])&/@pttns)]

alphaFactorial[alpha_umbra|alpha_Integer,nn_Integer]:=
With[{mod=Range[0,nn-1]},Expand[Times @@ (Identity/@(alpha-mod))]]

subDivisions[mSet_?VectorQ]:=
With[{partitions=IntegerPartitions/@mSet},partitions]


prepTerm[nn_Integer,gamma_umbra,multiplicities_List,ii_Integer]:=
With[{simUmbras=Table[makeSimilar[gamma],{Length[multiplicities]}]},
termFactor[nn,multiplicities]*termDotPows[simUmbras,multiplicities]]

termDotPows[umbras_List,multiplicities_List]:=
With[{raised=MapThread[#1^#2&,{umbras,Range[Length[multiplicities]]}]},
(Times @@MapThread[dotPower,{raised,multiplicities}])]/;
And[Length[umbras]==Length[multiplicities]]


(*
termFactor[alpha_umbra,multiplicities_List]:=
With[{facPart=ee[alpha^Length[multiplicities]]/
(mLambdaFactorial[multiplicities]*
lambdaFactorial[multiplicities])},
facPart]

*)

powsOfDotProduct[alpha_umbra,gamma_umbra,ii_Integer]:=
With[{pttns=cmpMultiplicities/@IntegerPartitions[ii]},
Plus @@	((Factorial[ii]*prepTerm[alpha,gamma,#,ii])&/@pttns)]

dotProduct[alpha_umbra,gamma_umbra]:=
umbra[Function[ii,ee[powsOfDotProduct[alpha,gamma,ii]]],{}]

prepTerm[alpha_umbra,gamma_umbra,multiplicities_List,ii_Integer]:=
With[{simUmbras=Table[makeSimilar[gamma],{Length[multiplicities]}]},
termFactor[alpha,multiplicities]*termDotPows[simUmbras,multiplicities]]


termFactor[alpha_umbra,multiplicities_List]:=
With[{facPart=alphaFactorial[alpha,(Plus @@multiplicities)]/
(mLambdaFactorial[multiplicities]*
lambdaFactorial[multiplicities])},
facPart]





makeSimilar[anUmbra_]:=With[{theOldArgs=getAllArgs[anUmbra]},
	With[{simSubs=Thread[theOldArgs->Table[Unique["umbraArg"],{Length[theOldArgs]}]]},
		anUmbra/.simSubs]]
	
	
	
(*lower factorial   x(x-1)(x-2)...(x-n+1) FactorialPower  *)
(*E^(alpha * z) is gen function*)
uniFa[alpha_umbra,gamma_umbra,ii_Integer]:=
With[{pttns=cmpMultiplicities/@IntegerPartitions[ii]},(Factorial[ii]*prepTerm[alpha,gamma,#,ii])&/@pttns]


cmpMultiplicities[aPartition_List]:=
With[{sum=Plus @@ aPartition},
Count[aPartition,#]&/@Range[sum]]//.{xx__,0}->{xx}


Unprotect[KroneckerDelta];
KroneckerDelta/:KroneckerDelta[0, nn_]^pp:=KroneckerDelta[0, nn]/;pp>=0
Protect[KroneckerDelta];

ff[anUmbra_]:=ee[anUmbra^#]&/@Range[0,10]


allSubdivisions[mulSet_?VectorQ]:=
With[{len=Plus@@mulSet},
With[{allSetParts=SetPartitions[len]},
	Union[Sort/@(allSetParts/.makeMultSubs[mulSet])]]]
	
makeMultSubs[mulSet_?VectorQ]:=
With[{len=Plus@@mulSet},
With[{from=Range[len],
	to=Flatten[Join[MapIndexed[Table[#2[[1]],{#1}]&,mulSet]]]},
	Thread[from->to]]]


kFori[theI_?VectorQ,nn_Integer]:=
With[{vLen=Length[theI],
prtns=Select[allSubdivisions[theI],(Length[#]<=nn)&]},	Flatten[
Permutations/@Flatten[padList[#,nn]&/@
	(useDoCount[#,vLen]&/@prtns),0],1]]

doCount[aVec_?VectorQ,aRng_Integer]:=
Count[aVec,#]&/@Range[aRng]

useDoCount[aSub_List,aRng_Integer]:=
doCount[#,aRng]&/@aSub
	
	
	
usePadList[multVecs_List,nn_Integer]:=
Flatten[Permutations[padList[#,nn]]&/@multVecs,1]


padList[amat_?MatrixQ,nn_Integer]:=
Join[amat,ConstantArray[0,{nn-Length[amat],Length[amat[[1]]]}]]


MFB[mIndex_?VectorQ]:=
MFB[mIndex]=
With[{mTab=allSubdivisions[mIndex]},
Plus @@ ((cmpFDrvs[mTab])*(cmpGDrvs[mTab,Length[mIndex]]))]

cmpFDrvs[mTab_List]:=$ff[{Length[#]}]&/@mTab

cmpGDrvs[mTab_List,numArgs_Integer]:=
With[{mults=multiplicity/@mTab},
mults*(cmpGTerms[#,numArgs]&/@mTab)]
	
Protected[$gg,$ff]

cmpGContribs[theList_?VectorQ,numArgs_Integer]:=
With[{todo=Union[theList],tmplte=ConstantArray[0,{numArgs}]},
With[{drvs=Count[theList,#]&/@todo},
With[{theRes=MapThread[ReplacePart[tmplte,#1->#2]&,{todo,drvs}]},
($gg[Plus@@theRes])]]]

cmpGTerms[theList_List,numArgs_Integer]:=
Times @@ (cmpGContribs[#,numArgs]&/@theList)


hardyDoubleFac[mSet_?VectorQ]:=
With[{theMax=Max[Flatten[mSet]]},
With[{theCounts=Count[mSet,#]&/@Range[theMax]},
	Times @@ (Factorial/@theCounts)]]

multiplicity[mSet_List]:=
If[mSet==={},1,
With[{totTau=Sort[Join@@mSet],oneTime=Union[mSet]},
With[{theMax=Last[totTau]},
With[{theCounts=Count[totTau,#]&/@Range[theMax],
	denomCounts=Count[mSet,#]&/@oneTime},
With[{numerator=Times @@ (Factorial/@theCounts)},
With[{firstHalf=Times@@
	Thread[(hardyDoubleFac/@oneTime)^denomCounts],
	secondHalf=Times @@ (Factorial/@denomCounts)},
With[{denominator=firstHalf*secondHalf},
numerator/denominator]]]]]]]


joint[drvs_?MatrixQ]:=
With[{mfbRes=MFB/@drvs,theR=cmpR[drvs],theS=cmpS[drvs]},
With[{subbedMfb=
MapIndexed[#/.{$gg[xx_]->$gg[#2[[1]],xx],$ff[xx_]->$ff[#2[[1]]]^xx}&,mfbRes]},
	(theR/theS)* (Times @@ subbedMfb)]]



	cmpR[drvs_?MatrixQ]:=
	With[{theSums= Plus @@ drvs},
		Times	@@(Factorial /@ theSums)]
		
		cmpS[drvs_?MatrixQ]:=Times @@ (Factorial/@Flatten[drvs])

UMFB[drv_?VectorQ,numGs_Integer]:=
With[{allDrvs=kFori[drv,numGs]},
	With[{allProds=joint/@allDrvs},
		With[{theSum= (Plus @@allProds)[[1]]//Expand},
			With[{fSums=Plus @@ ( toSum /@theSum)},
				With[{toSubs=fSums/.powsToSubs[numGs]},
					With[{toF=Plus @@ ((#//.sumToF)&/@toSubs)},
						toF
			]]]]]]
		
toSum[aTerm_]:=With[{theFs=Cases[aTerm,umbralCalculus`$ff[ii_]^pp_.],notFs=DeleteCases[List @@(aTerm),umbralCalculus`$ff[ii_]^pp_.]},
	(Plus @@ theFs)*(Times @@ notFs)]
		
timesToSum=Times[beg___,umbralCalculus`$ff[ii_]^pp_.,umbralCalculus`$ff[jj_]^qq_.,rest___]->
Times[(umbralCalculus`$ff[ii]^pp+umbralCalculus`$ff[jj]^qq),beg,rest]

sumToF={Plus[beg___,umbralCalculus`$ff[xx_],mid___,umbralCalculus`$ff[yy_],rest___]:>umbralCalculus`$ff[xx+yy]+beg+mid+rest}
powsToSubs[nn_Integer]:=
	{umbralCalculus`$ff[ii_]^pp_.:>umbralCalculus`$ff[ReplacePart[Table[0,{nn}],ii->pp]]
	}


lambdaSumsForGivenNu[nu_List,ff_?MatrixQ,gg_?MatrixQ]:=
With[{numGs=Length[gg]},
With[{allDrvs=kFori[nu,numGs]},
With[{allProds=joint/@allDrvs},
With[{theSum= (Plus @@Flatten[allProds])+$inCaseOnlyOneTerm//Expand},
With[{fSums=(Plus @@ ( toSum /@theSum))+$inCaseOnlyOneTerm},
With[{toSubs=fSums/.powsToSubs[numGs]},
With[{toF=(Plus @@ ((#//.sumToF)&/@toSubs))-$inCaseOnlyOneTerm},
	With[{gSubbed=(toF/.umbralCalculus`$gg[ii_Integer,mIndx_]:>
gg[[ii,theIndex[mIndx]]])},
With[{fSubbed=gSubbed/.(
	umbralCalculus`$ff[mIndx_]:>#[[theIndex[mIndx]]])&/@
	ff},
	fSubbed]]]]]]]]]
	
lambdaFacetDiffOrder[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
With[{allNu=Flatten[Join[allLambda[gArgs,#]&/@{diffOrder}],1]},Transpose[lambdaSumsForGivenNu[#,ff,gg]&/@allNu]]/;
And[Length[gg[[1]]]>=pascal[diffOrder,gArgs]-1,Length[ff[[1]]]>=pascal[diffOrder,Length[gg]]-1]

lambdaFacetDiffOrder[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
With[{},
	Print[StringForm["With diffOrder=`` gArgs=`` gMat should have at least `` columns and exactly `` rows. fMat should have at least `` columns",
		 diffOrder,gArgs,pascal[diffOrder,gArgs]-1,gArgs,pascal[diffOrder,Length[gg]]-1]]]

allLambda[mm_Integer,nn_Integer]:=Reverse[Compositions[nn,mm]]


	
lambdaSumsDiffOrder[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
With[{allNu=Flatten[Join[allLambda[gArgs,#]&/@Range[diffOrder]],1]},Transpose[lambdaSumsForGivenNu[#,ff,gg]&/@allNu]]/;
And[Length[gg[[1]]]>=pascal[diffOrder,gArgs]-1,Length[ff[[1]]]>=pascal[diffOrder,Length[gg]]-1]

lambdaSumsDiffOrder[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
With[{},
	Print[StringForm["With diffOrder=`` gArgs=`` gMat should have at least `` columns and exactly `` rows. fMat should have at least `` columns",
		 diffOrder,gArgs,pascal[diffOrder,gArgs]-1,gArgs,pascal[diffOrder,Length[gg]]-1]]]

applyFaDiBruno[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
lambdaSumsDiffOrder[diffOrder,gArgs,ff,gg]	

End[]

EndPackage[]

