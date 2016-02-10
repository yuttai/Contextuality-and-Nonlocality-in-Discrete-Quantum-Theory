(* ::Package:: *)

(* ::Section:: *)
(*I. Introduction*)


(* ::Section:: *)
(*II. Fundamentals of Finite Fields*)


cModOffset[p_Integer]:=-((p-1)/2);
cLogOffset[p_Integer]:=-((p^2-1)/2)+1;


cMod[x_,0]:=cMod[x,0]=ToRadicals[FullSimplify[x]]
GaussianIntegerQ[x_]:=GaussianIntegerQ[x]=IntegerQ[Re[x]]\[And]IntegerQ[Im[x]]
cMod[x_?GaussianIntegerQ,p_Integer]:=cMod[x,p]=Mod[Re[x],p,cModOffset[p]]+I Mod[Im[x],p,cModOffset[p]]
SetAttributes[cMod,Listable]
cBasis[p_Integer]:=cBasis[p]=Flatten[Table[x+I y,{x,cModOffset[p],cModOffset[p]+p-1},{y,cModOffset[p],cModOffset[p]+p-1}]]
cBasis::usage="List all elements in \!\(\*SubscriptBox[\[DoubleStruckCapitalF], SuperscriptBox[\(p\), \(2\)]]\)";
cBasis[3]


(* ::Text:: *)
(*Galois generator list:*)


cFindGens[p_Integer]:=cFindGens[p]=Module[{base=Complement[cBasis[p],{0}],test,out={}},Do[test=Table[cMod[b^k,p],{k,1,p^2-1}];
If[Sort[base]==Sort[test],AppendTo[out,b]],{b,base}];
out]


(* ::Text:: *)
(*and the number of generators is EulerPhi[p^2-1].*)


defaultGenerators[p_Integer]:=defaultGenerators[p]=Switch[p,0,Indeterminate,3,1-I,7,3+I,11,5+4I,19,9+6 I,23,11+10I,31,15+13 I,43,21+19 I]


(* ::Text:: *)
(*Before we define log in DQC, it is a good chance to discuss how to define Subscript[log, 1]x, or in general the domain and range of Subscript[log, b]x. In Mathematica and intuitively, it is easy to define Subscript[log, b]x:=(ln x)/(ln b). However, if we admit the principal value of ln as ln:\[DoubleStruckCapitalC]\{0}->\[DoubleStruckCapitalR]+I[-\[Pi],\[Pi]] or more easily \[Lambda] x.((ln x)/(2\[Pi] I)):S^1->[-(1/2),1/2], then the principal of log is \[Lambda] b.\[Lambda] x.Subscript[log, b]x=(ln x)/(ln b):S^1\[Cross]S^1->\[DoubleStruckCapitalR]\[Union]{\[Infinity]} . However, if we use the principal branch, Subscript[log, 1](-1) is undefined or \[Infinity], but -1 is a second root of unity, i.e., (-1)^2=1. Is it reasonable to define Subscript[log, 1](-1)=1/2? Or in general, *)
(*Log[1,x]=Log[-1,x]/Log[-1,1]=Log[-1,x]/2=Log[x]/(2Log[-1])=Log[x]/(2\[Pi] I) ?*)


cPower[z_,r_Integer,p_Integer]:=cPower[z,r,p]=If[p==0,z^r,If[cMod[z,p]==0,If[r>0,0,Indeterminate],cMod[z^Mod[r ,p^2-1],p]]]
cPower[z_,r_Integer,p_Integer,g_]:=cPower[z,r,p,g]=cPower[z,r,p]
cLog::usage="Noticed that this is only the principal value of Log... In general, \!\(\*SuperscriptBox[\(b\), \(\*SuperscriptBox[\(p\), \(2\)] - 1 + Log[z]\)]\)\[Equal]\!\(\*SuperscriptBox[\(b\), \(Log[z]\)]\)\[Equal]z";
cLog[b_,z_,p_Integer,g_]:=cLog[b,z,p,g]=If[p==0,Log[b,z],If[b==g,
Switch[cMod[z,p],
0,\[Infinity],
1,0,
_,Mod[1+cLog[g,cMod[z cPower[g,-1,p],p],p,g],p^2-1,cLogOffset[p]]],cLog[g,z,p,g]/cLog[g,b,p,g]]]
cLog[b_,z_,p_Integer]:=cLog[b,z,p]=cLog[b,z,p,defaultGenerators[p]]
cLog[z_,p_Integer]:=cLog[z,p]=cLog[defaultGenerators[p],z,p]
cPower::usage="Noticed that this is only the principle value of Power...";
cPower[z_,r_Rational,p_Integer,g_]:=cPower[z,r,p,g]=If[p==0,z^r,If[cMod[z,p]==0,If[r>0,0,Indeterminate],If[IntegerQ[r cLog[g,z,p,g]],cMod[g^Mod[r cLog[g,z,p,g],p^2-1],p],Indeterminate]]]
cPower[z_,r_Rational,p_Integer]:=cPower[z,r,p]=cPower[z,r,p,defaultGenerators[p]]
Function[{g},cPower[g,#,3]&/@Range[0,7]]/@{1+I,1-I,-1+I,-1-I}
cPower[-1,#,3]&/@{1/1,1/2,3/2,1/4,3/4,5/4,7/4}
cLog::usage="\!\(\*SuperscriptBox[\(b\), \(cLog\)]\)\[Equal]z";
({#,cLog[#,3]}&/@cBasis[3])//TableForm


cMod[x_?(\[Not]GaussianIntegerQ[#]&),p_Integer]:=Switch[Head[x],
Rational,cMod[Numerator[x]cPower[Denominator[x],-1,p],p],
Complex,cMod[Re[x],p]+I cMod[Im[x],p],
Plus,cMod[#,p]&/@x,
Times,cMod[#,p]&/@x,
Power,cPower[cMod[x[[1]],p],x[[2]],p],
Root,If[Head[#]==Root,Dialog[],cMod[#,p]]&[ToRadicals[x]],
_,x]
cMod[(3 I)(4-4 I),11]
cMod[1/Sqrt[6],11]
cMod[(-1)^(1/4),11]
cMod[1/Sqrt[6] (-1)^(1/4),11]
cMod[-(1/2),3]
cMod[1/3,3]
cMod[(6+I Sqrt[5])^(1/3),#]&/@{0,3,7,11,19,23}


Select[cBasis[3],cMod[#\[Conjugate]#,3]==1&]
cFieldNorm[z_,p_Integer]:=cFieldNorm[z,p]=If[p==0,z\[Conjugate]z,cPower[z,p+1,p]]
cFNormInv[z_,p_Integer]:=If[p==0,Sqrt[z],cPower[z,1/(p+1),p]]
cFNormInv[z_,p_Integer,g_]:=cFNormInv[z,p,g]=If[p==0,Sqrt[z],cPower[z,1/(p+1),p,g]]
({#,cLog[#,3],cLog[#,3]/(3+1),cFNormInv[#,3]}&/@Range[-1,1])//TableForm
({#,cLog[#,7],cLog[#,7]/(7+1),cFNormInv[#,7]}&/@Range[-3,3])//TableForm
{#,Select[cBasis[7],Function[{x},cMod[x\[Conjugate]x,7]==#]]}&/@Range[-3,3]
cFNormInv[4-2 Sqrt[2],0]


cMultiplicativeGroup[p_Integer]:=cMultiplicativeGroup[p]=Complement[cBasis[p],{0}]
cMultiplicativeGroup[3]


cUnitCirle[p_Integer]:=cUnitCirle[p]=
Select[cMultiplicativeGroup[p],cMod[#\[Conjugate]#,p]==1&]
cUnitCirle[3]


(* ::Section:: *)
(*III. Schwinger Basis*)


\[Omega][p_Integer,d_Integer]:=\[Omega][p,d]=If[p==0,E^((2\[Pi] I)/d),\[Omega][p,d,defaultGenerators[p]]]
\[Omega][p_Integer,d_Integer,g_]:=\[Omega][p,d,g]=If[p==0,E^((2\[Pi] I)/d),cPower[g,(p^2-1)/d,p]]
uMat[p_Integer,d_Integer]:=uMat[p,d]=uMat[p,d,defaultGenerators[p]]
uMat[p_Integer,d_Integer,g_]:=uMat[p,d,g]=
DiagonalMatrix[cMod[\[Omega][p,d,g]^#,p]&/@Range[0,d-1]]
vMat[d_Integer]:=vMat[d]=RotateLeft[IdentityMatrix[d]]
vMat[p_Integer,d_Integer]:=vMat[d]
MatrixForm/@Prepend[uMat[#,2]&/@{0,3,7,11,19,23,31},vMat[2]]
MatrixForm/@Prepend[uMat[#,3]&/@{0,11,23},vMat[3]]
MatrixForm/@Prepend[uMat[#,4]&/@{0,3,7,11,19,23,31},vMat[4]]
MatrixForm/@Prepend[uMat[#,5]&/@{0,19},vMat[5]]
MatrixForm/@Prepend[uMat[#,6]&/@{0,11,23},vMat[6]]
MatrixForm/@Prepend[uMat[#,8]&/@{0,7,23,31},vMat[8]]


cRowReduce[A_,p_Integer]:=cRowReduce[A,p]=
Module[{a=cMod[A,p],Col,iMin,Row1=1},
Do[
(*Find pivot for column k:*)
iMin=Row1-1+Position[a[[Row1;;,Col]],Except[0,_?NumberQ]];
If[iMin!={},
iMin=iMin[[1]][[1]];
{a[[Row1]],a[[iMin]]}={a[[iMin]],a[[Row1]]};
a[[Row1]]=cMod[a[[Row1]]cPower[a[[Row1,Col]],-1,p],p];
(*Do for all rows below pivot:*)
(*Do for all remaining elements in current row:*)
(*'Fill lower triangular matrix with zeros:*)
a[[;;Row1-1,Col;;]]=cMod[a[[;;Row1-1,Col;;]]-KroneckerProduct[a[[;;Row1-1,Col]],a[[Row1,Col;;]]],p];
a[[Row1+1;;,Col;;]]=cMod[a[[Row1+1;;,Col;;]]-KroneckerProduct[a[[Row1+1;;,Col]],a[[Row1,Col;;]]],p];
Row1++;
If[Row1>Dimensions[a][[1]],Break[]]],
{Col,Dimensions[a][[2]]}];a]
cRowReduce[{{2,-4,2,-2},{2,-4,3,-4},{4,-8,3,-2},{0,0,-1,2}},23]
cRowReduce[{{1,0,4},{2,0,3},{2,1,2}}, 5]
cRowReduce[{{1,-2,1,-1},{2,-3,4,-3},{3,-5,5,-4},{-1,1,-3,2}},23]
cRowReduce[{{1-I,1-I},{1-I,1-I}},3]


cMatrixPower[m_,r_Integer,p_Integer]:=cMatrixPower[m,r,p]=If[r>=0,cMod[MatrixPower[m,r],p],Module[{a=cRowReduce[Join[m,IdentityMatrix[Length[m]],2],p]},
If[a[[;;,;;Length[m]]]==IdentityMatrix[Length[m]],cMod[MatrixPower[a[[;;,Length[m]+1;;]],-r],p],Indeterminate]]]
cMatrixPower[\!\(\*
TagBox[
RowBox[{"(", GridBox[{
{
RowBox[{
RowBox[{"-", "1"}], "-", "I"}], 
RowBox[{
RowBox[{"-", "1"}], "-", "I"}]},
{
RowBox[{
RowBox[{"-", "1"}], "-", "I"}], 
RowBox[{"1", "+", "I"}]}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}}], ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\),-1,3]//MatrixForm
cMatrixPower[m_,d_Integer,p_Integer,g_]:=cMatrixPower[m,d,p]
cMatrixPower[\!\(\*
TagBox[
RowBox[{"(", GridBox[{
{"0", "0"},
{"0", "1"}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}}], ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\),2,3]//MatrixForm


(* ::Text:: *)
(*Claim 1. U^d=1=v^d*)


MatrixForm/@MapThread[cMatrixPower[#1,2,#2]==IdentityMatrix[2]&,{{vMat[2],uMat[3,2],uMat[7,2],uMat[11,2]},{3,3,7,11}}]
MatrixForm/@MapThread[cMatrixPower[#1,3,#2]==IdentityMatrix[3]&,{{vMat[3],uMat[11,3]},{11,11}}]
MatrixForm/@MapThread[cMatrixPower[#1,4,#2]==IdentityMatrix[4]&,{{vMat[4],uMat[3,4],uMat[7,4],uMat[11,4]},{3,3,7,11}}]


(* ::Text:: *)
(*Claim 2. VU=\[Omega]UV*)


claim2[p_Integer,d_Integer]:=cMod[vMat[d].uMat[p,d]-\[Omega][p,d] uMat[p,d].vMat[d],p]==ConstantArray[0,{d,d}]
MapThread[claim2,{{3,7,11,19,11,3,7,11,19,19},{2,2,2,2,3,4,4,4,4,5}}]


(* ::Text:: *)
(*Claim 3. det U=(-1)^(d-1)=det V*)


claim3[p_Integer,d_Integer]:=cMod[Det[vMat[d]],p]==cMod[(-1)^(d-1),p]\[And]cMod[Det[uMat[p,d]],p]==cMod[(-1)^(d-1),p]
MapThread[claim3,{{3,7,11,19,11,3,7,11,19,19},{2,2,2,2,3,4,4,4,4,5}}]


UnitMatrix[{i_Integer,j_Integer},{m_Integer,n_Integer}]:=UnitMatrix[{i,j},{m,n}]=KroneckerProduct[UnitVector[m,i],UnitVector[n,j]]
UnitMatrix[{2,3},{3,3}]//MatrixForm


claim4[p_Integer,d_Integer]:=And@@(UnitMatrix[{#+1,#+1},{d,d}]==cMod[cPower[d,-1,p]\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(i = 0\), \(d - 1\)]\(cPower[\[Omega][p, d], \(-i\) #, p] cMatrixPower[uMat[p, d], i, p]\)\),p]&/@Range[0,d-1])
MapThread[claim4,{{3,7,11,19,11,3,7,11,19,19},{2,2,2,2,3,4,4,4,4,5}}]


claim5[p_Integer,d_Integer]:=And@@(UnitMatrix[{#[[1]]+1,#[[2]]+1},{d,d}]==cMod[cPower[d,-1,p]\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(i = 0\), \(d - 1\)]\(cPower[\[Omega][p, d], \(-i\) #[\([1]\)], p] cMatrixPower[uMat[p, d], i, p] . cMatrixPower[vMat[d], #[\([2]\)] - #[\([1]\)], p]\)\),p]&/@Tuples[Range[0,d-1],2])
MapThread[claim5,{{3,7,11,19,11,3,7,11,19,19},{2,2,2,2,3,4,4,4,4,5}}]


fMat[p_Integer,d_Integer]:=fMat[p,d,defaultGenerators[p]]
fMat[p_Integer,d_Integer,g_]:=(cMod[Array[\[Omega][p,d,g]^((#1-1)(#2-1))&,{d,d}] cPower[cFNormInv[d,p,g],-1,p,g],p])\[ConjugateTranspose]
MatrixForm/@(fMat[#,2]&/@{0,3,7,11,19,23,31})
MatrixForm/@(fMat[#,3]&/@{0,11,23})
MatrixForm/@(fMat[#,4]&/@{0,3,7,11,19,23,31})
MatrixForm/@(fMat[#,5]&/@{(*0,*)19})
MatrixForm/@(fMat[#,6]&/@{0,11,23})
MatrixForm/@(fMat[#,8]&/@{0,7,23,31})
MatrixForm/@Module[{d=3,p=11},{cFNormInv[d,p],cMod[Array[\[Omega][p,d]^((#1-1)(#2-1))&,{d,d}],p]}]


claim7[p_Integer,d_Integer]:=cMod[fMat[p,d]\[ConjugateTranspose].fMat[p,d],p]==IdentityMatrix[d]
MatrixForm/@(claim7[#,2]&/@{0,3,7,11,19,23,31})
MatrixForm/@(claim7[#,3]&/@{0,11,23})
MatrixForm/@(claim7[#,4]&/@{0,3,7,11,19,23,31})
MatrixForm/@(claim7[#,5]&/@{(*0,*)19})
MatrixForm/@(claim7[#,6]&/@{0,11,23})
MatrixForm/@(claim7[#,8]&/@{0,7,23,31})


claim8[p_Integer,d_Integer]:=cMod[fMat[p,d].uMat[p,d]\[ConjugateTranspose].fMat[p,d]\[ConjugateTranspose],p]==vMat[d]\[And]cMod[fMat[p,d]\[ConjugateTranspose].uMat[p,d].fMat[p,d],p]==vMat[d]
MatrixForm/@(claim8[#,2]&/@{0,3,7,11,19,23,31})
MatrixForm/@(claim8[#,3]&/@{0,11,23})
MatrixForm/@(claim8[#,4]&/@{0,3,7,11,19,23,31})
MatrixForm/@(claim8[#,5]&/@{(*0,*)19})
MatrixForm/@(claim8[#,6]&/@{0,11,23})
MatrixForm/@(claim8[#,8]&/@{0,7,23,31})


(* ::Section:: *)
(*IV. Diagoniability of Unitary Matrix*)


cPolynomialMod[poly_,x_,p_Integer]:=cPolynomialMod[poly,x,p]=FromDigits[Reverse[cMod[CoefficientList[poly,x],p]],x]


cPolynomialQuotient[poly1_,poly2_,x_,p_Integer]:=cPolynomialQuotient[poly1,poly2,x,p]=If[Exponent[poly1,x]<0,0,
#+cPolynomialQuotient[cPolynomialMod[poly1-poly2 #,x,p],poly2,x,p]&[cPolynomialMod[Coefficient[poly1,x,Exponent[poly1,x]]cPower[Coefficient[poly2,x,Exponent[poly2,x]],-1,p],x,p]x^(Exponent[poly1,x]-Exponent[poly2,x])]]
Module[{x},cPolynomialQuotient[x^2+4 x+1,2x+1,x,3]]


cSolveInFpSquare[poly_,x_,p_Integer]:=cSolveInFpSquare[poly,x,p]=
If[#=={},{},Join[#,cSolveInFpSquare[cPolynomialQuotient[poly,Product[x-i,{i,#}],x,p],x,p]]]&[Select[cBasis[p],cMod[poly/.x->#,p]==0&]]
Module[{x},{cSolveInFpSquare[x^2,x,3],cSolveInFpSquare[-x^2+x+1,x,3]}]


cEigenvalues[m_,p_Integer]:=cEigenvalues[m,p]=If[p==0,FullSimplify[Eigenvalues[m]],If[FreeQ[m,_Symbol,Heads->False],Module[{x},
cSolveInFpSquare[PolynomialMod[CharacteristicPolynomial[m,x],p],x,p]],cMod[Eigenvalues[m],p]]]
cEigenvalues[({
 {1, 0},
 {0, 1}
}),3]
Module[{x1,x2},cEigenvalues[({
 {x1, 0},
 {0, x2}
}),3]]


cNullSpace[m_,p_Integer]:=If[p==0,NullSpace[m],Module[{a=cRowReduce[m,p],v,Row2Column=ConstantArray[0,Dimensions[m][[2]]],basis={},Col,iMin,Row1},
Do[
iMin=Position[a[[;;,Col]],Except[0,_?NumberQ]];
If[Length[iMin]==1\[And]a[[iMin[[1,1]],Col]]==1\[And]Row2Column[[iMin[[1,1]]]]==0,
Row2Column[[iMin[[1,1]]]]=Col,
v=UnitVector[Dimensions[a][[2]],Col];
Do[v[[Row2Column[[Row1[[1]]]]]]=-a[[Row1[[1]],Col]],{Row1,iMin}];
AppendTo[basis,v]],
{Col,Dimensions[a][[2]]}];basis]]
cNullSpace[{{0,0,0,0},{0,1,0,0},{0,0,-1,0},{0,0,0,0}},3]
cNullSpace[{{1,-2,1,-1},{2,-3,4,-3},{3,-5,5,-4},{-1,1,-3,2}},23]
cNullSpace[{{1,0,4},{2,0,3},{2,1,2}},5]
cNullSpace[{{1-I,1-I},{1-I,1-I}},3]
cNullSpace[{{1,0},{0,1}},3]


cInvertible[m_,p_Integer]:=cNullSpace[m,p]=={}
cInvertible[{{1,0},{0,1}},3]


cLinearSolve[m_,b_,p_Integer]:=cLinearSolve[m,b,p]=If[#=={},{},cMod[-cPower[#[[1,-1]],-1,p]#[[1,;;-2]],p]]&[Select[cNullSpace[Join[m,{b}\[Transpose],2],p],#[[-1]]!=0&]]
cLinearSolve[{{1,1,1},{1,2,3},{1,4,9}},{1,2,3},47]
cMod[{{1,1,1},{1,2,3},{1,4,9}}.{23,2,23},47]=={1,2,3}


cVectors2Representative[v_,p_]:=Module[{i=Cases[cMod[v,p],Except[0],1,1]},If[i=={},v,cMod[v cPower[i[[1]],-1,p],p]]]


cNormalize[v_,p_Integer]:=
cNormalize[v,p]=Module[{v1=cVectors2Representative[v,p]},If[p==0,Normalize[v1],If[cMod[v1\[Conjugate].v1,p]==0,v1,cMod[cPower[cFNormInv[v1\[Conjugate].v1,p],-1,p]v1,p]]]]
cNormalize[{-1+I,1},3]
cNormalize[{-1+I,1},0]
cNormalize[{1-Sqrt[2],1},0]


cTranspose[m_]:=Switch[Length[Dimensions[m]],0,{{}},1,{m},_,m\[Transpose]]
cTranspose[{}]
cTranspose[{1,2}]


cVectorsInSubspace[basis_List,p_Integer]:=cMod[basis\[Transpose].#,p]&/@Tuples[cBasis[p],Length[basis]]


cRadicalDimension[basis_List,p_Integer]:=Log[p^2,Count[cVectorsInSubspace[basis,p],_?cMod[#.basis\[ConjugateTranspose],p]==ConstantArray[0,Length[basis]]&]]


cUnitNormVectorsInSubspace[basis_,p_Integer]:=Select[cVectorsInSubspace[basis,p],cMod[#\[Conjugate].#,p]==1&]
cUnitNormVectorsInSubspace[IdentityMatrix[2],3]
cUnitNormVectorsInSubspace[{{-1-I,-1-I,0},{-1-I,0,1}},3]
cUnitNormVectorsInSubspace[{{-1-I,1}},3]


cUnitNormVectors[p_Integer,d_Integer]:=cUnitNormVectors[p,d]=cUnitNormVectorsInSubspace[IdentityMatrix[d],p]
cUnitNormVectors[3,2]


(*groupOrbits, SplitBy*)
groupOrbits::usage="G={G,*}"<>
"For all g in G, \!\(\*SubscriptBox[\(x\), \(1\)]\) in X, we have f[g,\!\(\*SubscriptBox[\(x\), \(1\)]\)]=\!\(\*SubscriptBox[\(x\), \(2\)]\)";
groupOrbits[G_(*group*),X_(*set*),f_(*action*)]:=groupOrbits[G,X,f]=
Module[{orbits={},x},
Do[If[FreeQ[orbits,x,{2}],orbits=Append[orbits,DeleteDuplicates[f[#,x]&/@G]]],{x,X}];
orbits]
(*The following example is exactly the same as getHopfMapGroups.*)
groupOrbits[cUnitCirle[3],cUnitNormVectors[3,2],cMod[#1 #2,3]&]


groupOrbitsRepresentative[G_(*group*),X_(*set*),f_(*action*),RepresentativeFunction_]:=groupOrbitsRepresentative[G,X,f,RepresentativeFunction]=RepresentativeFunction[First[#]]&/@groupOrbits[G,X,f]
groupOrbitsRepresentative[cUnitCirle[3],cUnitNormVectors[3,2],cMod[#1 #2,3]&,cNormalize[#,3]&]


cUnitNormVectorsRepresentativeInSubspace[basis_,p_Integer]:=groupOrbitsRepresentative[cUnitCirle[p],cUnitNormVectorsInSubspace[basis,p],Function[{g,x},cMod[g #,p]&/@x],cNormalize[#,p]&]
cUnitNormVectorsRepresentativeInSubspace[IdentityMatrix[2],3]
cUnitNormVectorsRepresentativeInSubspace[{{-1-I,-1-I,0},{-1-I,0,1}},3]
cUnitNormVectorsRepresentativeInSubspace[{{-1-I,1}},3]


cUnitNormVectorsRepresentative[p_Integer,d_Integer]:=cUnitNormVectorsRepresentative[p,d]=cUnitNormVectorsRepresentativeInSubspace[IdentityMatrix[d],p]
(*cUnitNormVectorsRepresentative[p,d]=groupOrbitsRepresentative[cUnitCirle[p],cUnitNormVectors[p,d],Function[{g,x},cMod[g#,p]&/@x],cNormalize[#,p]&]*)
cUnitNormVectorsRepresentative[3,2]
Length[cUnitNormVectorsRepresentative[3,3]]


cRightAngleVectors[vector_,basis_,p_]:=cRightAngleVectors[vector,basis,p]=Select[cUnitNormVectorsRepresentativeInSubspace[basis,p],cMod[vector\[Conjugate].#,p]==0&]
cOrthonormalSets[set_,possibleVectors_,basis_,p_,f_]:=If[possibleVectors=={},{f[set]},Flatten[cOrthonormalSets[Append[set,#],possibleVectors\[Intersection]cRightAngleVectors[#,basis,p],basis,p,f]&/@possibleVectors,1]];
cOrthonormalSets[{{-1-I,-1-I,0}},Select[cUnitNormVectorsRepresentativeInSubspace[{{-1-I,-1-I,0},{-1,-2,1}},3],cMod[{{-1-I,-1-I,0}}\[Conjugate].#,3]==ConstantArray[0,1]&],{{-1-I,-1-I,0},{-1,-2,1}},3,#&]
cOrthonormalSets[{},Select[cUnitNormVectorsRepresentativeInSubspace[{{-1-I,1}},3],True&],{{-1-I,1}},3,#&]
cOrthonormalSets[{{-1-I,1+I,0}},Select[cUnitNormVectorsRepresentativeInSubspace[{{-1-I,1+I,0},{1,1,-1}},3],cMod[{{-1-I,1+I,0}}\[Conjugate].#,3]==ConstantArray[0,1]&],{{-1-I,1+I,0},{1,1,-1}},3,#&]
cOrthonormalSets[{{1,0,0,0},{0,1,1,1-I}},Select[cUnitNormVectorsRepresentativeInSubspace[{{1,0,0,0},{0,1,1,1-I},{0,-1,0,-1+I},{0,-1-I,-1-I,-1}},3],cMod[{{1,0,0,0},{0,1,1,1-I}}\[Conjugate].#,3]==ConstantArray[0,2]&],{{1,0,0,0},{0,1,1,1-I},{0,-1,0,-1+I},{0,-1-I,-1-I,-1}},3,#&]
First[cOrthonormalSets[{{-1-I,0,-1-I}},cRightAngleVectors[{-1-I,0,-1-I},IdentityMatrix[3],3],IdentityMatrix[3],3,#&]]


cFirstOrthonormalSet[set_List,possibleVectors_List,basis_List,p_Integer]:=Catch[cOrthonormalSets[set,possibleVectors,basis,p,If[Length[#]==Length[basis],Throw[#],#]&][[1]](*The last \[LeftDoubleBracket]1\[RightDoubleBracket] because we need type check if not throw anything...*)]
cFirstOrthonormalSet[{{-1-I,-1-I,0}},Select[cUnitNormVectorsRepresentativeInSubspace[{{-1-I,-1-I,0},{-1,-2,1}},3],cMod[{{-1-I,-1-I,0}}\[Conjugate].#,3]==ConstantArray[0,1]&],{{-1-I,-1-I,0},{-1,-2,1}},3]
cFirstOrthonormalSet[{},cUnitNormVectorsRepresentativeInSubspace[{{-1-I,1}},3],{{-1-I,1}},3]
cFirstOrthonormalSet[{{-1-I,1+I,0}},Select[cUnitNormVectorsRepresentativeInSubspace[{{-1-I,1+I,0},{1,1,-1}},3],cMod[{{-1-I,1+I,0}}\[Conjugate].#,3]==ConstantArray[0,1]&],{{-1-I,1+I,0},{1,1,-1}},3]
cFirstOrthonormalSet[{{1,0,0,0},{0,1,1,1-I}},Select[cUnitNormVectorsRepresentativeInSubspace[{{1,0,0,0},{0,1,1,1-I},{0,-1,0,-1+I},{0,-1-I,-1-I,-1}},3],cMod[{{1,0,0,0},{0,1,1,1-I}}\[Conjugate].#,3]==ConstantArray[0,2]&],{{1,0,0,0},{0,1,1,1-I},{0,-1,0,-1+I},{0,-1-I,-1-I,-1}},3]
cFirstOrthonormalSet[{{-1-I,0,-1-I}},cRightAngleVectors[{-1-I,0,-1-I},IdentityMatrix[3],3],IdentityMatrix[3],3]


cOrthonormalBasisInSubspace[basis_,p_Integer,f_]:=cOrthonormalSets[{},cUnitNormVectorsRepresentativeInSubspace[basis,p],basis,p,f]
Catch[cOrthonormalBasisInSubspace[IdentityMatrix[2],3,If[Length[#]==2,Throw[#],#]&]]
Catch[cOrthonormalBasisInSubspace[{{-1-I,-1-I,0},{-1-I,0,1}},3,If[Length[#]==2,Throw[#],#]&]]
Catch[cOrthonormalBasisInSubspace[{{-1-I,1}},3,If[Length[#]==1,Throw[#],#]&]]


cOrthonormalBasisInSubspace[basis_,p_Integer]:=cOrthonormalBasisInSubspace[basis,p]=cOrthonormalBasisInSubspace[basis,p,Identity]
cOrthonormalBasisInSubspace[IdentityMatrix[2],3]
cOrthonormalBasisInSubspace[{{-1-I,-1-I,0},{-1-I,0,1}},3]
cOrthonormalBasisInSubspace[{{-1-I,1}},3]
cOrthonormalBasisInSubspace[{{1,1,0},{1,0,1}},3]


cOrthogonalize[basis_List,p_Integer]:=cOrthogonalize[basis,p]=If[p==0,Orthogonalize[basis],
Module[{\[Phi]=basis,i},For[i=1,i<=Length[\[Phi]],i++,If[cMod[\[Phi][[i]]\[Conjugate].\[Phi][[i]],p]==0,\[Phi]=cFirstOrthonormalSet[\[Phi][[1;;i-1]],Select[cUnitNormVectorsRepresentativeInSubspace[\[Phi],p],If[i>1,cMod[\[Phi][[1;;i-1]]\[Conjugate].#,p]==ConstantArray[0,i-1],True]&],\[Phi],p],\[Phi][[i]]=cNormalize[\[Phi][[i]],p]];
If[i<Length[\[Phi]],\[Phi][[i+1;;Length[\[Phi]]]]-=(\[Phi][[i+1;;Length[\[Phi]]]].Outer[Times,\[Phi][[i]]\[Conjugate],\[Phi][[i]]])](*Gram-Schmidt process*)];
\[Phi]]]
cOrthogonalize[{{1,1,0},{1,0,1}},3]
cOrthogonalize[IdentityMatrix[2],3]
cOrthogonalize[{{-1-I,-1-I,0},{-1-I,0,1}},3]
cOrthogonalize[{{-1-I,1}},3]
cOrthogonalize[{{0,1}},3]
cOrthogonalize[{{1-I,-I,0,1},{0,I,1+I,1}},3]
cOrthogonalize[{{1,-1,0},{1,1,-1}},3]
cOrthogonalize[{{1,0,0,0},{0,1,1,1-I},{0,0,1,0},{0,0,0,1}},3]
cOrthogonalize[{{1,1,0},{1,0,1}},3]
cOrthogonalize[{{1,-1+I,0},{1,0,-1+I}},3]
cOrthogonalize[Prepend[IdentityMatrix[3],{1,1,0}],3]


cEigensystem[m_List,p_Integer]:=cEigensystem[m,p]=If[FreeQ[m,_Symbol,Heads->False],
Module[{\[Lambda]s=Sort[cEigenvalues[m,p]]},
{\[Lambda]s,cTranspose[Join@@(PadRight[Module[{
b=cNullSpace[m-#[[1]]IdentityMatrix[Length[m]],p],nb,ob},
If[p==0,
FullSimplify[cNormalize[#,p]]&/@Orthogonalize[b],
nb=cNormalize[#,p]&/@b;
ob=cOrthogonalize[nb,p];
If[Length[ob]<Length[nb],nb,ob]]],
{#[[2]],Length[m]}]&/@Tally[\[Lambda]s])]}],{cMod[#[[1]],p],cOrthogonalize[#[[2]],p]\[Transpose]}&[Eigensystem[m]]]
uMatEigensystem[p_Integer,d_Integer]:={#[[1]],MatrixForm[#[[2]]]}&[cEigensystem[uMat[p,d],p]]
MapThread[uMatEigensystem,{{0,3,7,11,19,0,11,0,3,7,11,19,19},{2,2,2,2,2,3,3,4,4,4,4,4,5}}]
vMatEigensystem[p_Integer,d_Integer]:={#[[1]],MatrixForm[#[[2]]]}&[cEigensystem[vMat[d],p]]
MapThread[vMatEigensystem,{{0,3,7,11,19,0,11,0,3,7,11,19,19},{2,2,2,2,2,3,3,4,4,4,4,4,5}}]
MapAt[MatrixForm,cEigensystem[{{0,0,0,0},{0,1,0,0},{0,0,-1,0},{0,0,0,0}},3],2]
MapAt[MatrixForm,cEigensystem[({
 {1/4, -(1/4)},
 {-(1/4), 3/4}
}),0],2]
MapAt[MatrixForm,cEigensystem[({
 {-1, -1},
 {-1, 0}
}),3],2]


cUnitaryGroup[p_Integer,d_Integer]:=cUnitaryGroup[p,d]=Module[{rightAngleVectors,vector,orthonormalSets,vectorConj,answer},
Do[vectorConj=vector\[Conjugate];rightAngleVectors[vector]=Select[cUnitNormVectors[p,d],cMod[vectorConj.#,p]==0&],{vector,cUnitNormVectors[p,d]}];
orthonormalSets[set_,possibleVectors_]:=If[possibleVectors=={},{set},Flatten[orthonormalSets[Append[set,#],possibleVectors\[Intersection]rightAngleVectors[#]]&/@possibleVectors,1]];
orthonormalSets[{},cUnitNormVectors[p,d]]]


cDiagonlizableTest[U_,p_Integer]:=cDiagonlizableTest[U,p]=
Which[
Length[#[[1]]]<Length[U],1,
\[Not]cInvertible[#[[2]],p],2,
MemberQ[#[[2]]\[ConjugateTranspose],ConstantArray[0,Length[#[[2]]]]],3,
cMod[#[[2]]\[ConjugateTranspose].#[[2]],p]!=IdentityMatrix[Length[U]],4,
True,5]&[cEigensystem[U,p]]
cDiagonlizableTest[IdentityMatrix[2],3]


cDiagonlizableExample[UG_,meaning_,p_Integer]:=
Module[{
U1={False,False,False,False,False},
U2={{},{},{},{},{}}},
Do[Module[{index=cDiagonlizableTest[A,p]},
U1[[index]]=True;
If[And@@U1,Break[]];
If[U2[[index]]=={}\[Or]Max[Abs[A]]<Max[Abs[U2[[index]]]],U2[[index]]=A]],{A,UG}];
Join[meaning,{", Total Number: ",Length[UG],"\n"},Join@@(If[U1[[#]],Join[cDiagonlizableExplain[U2[[#]],p],{" in \!\(\*SubscriptBox[\(\[DoubleStruckCapitalF]\), SuperscriptBox[\(p\), \(2\)]]\)\n"},cDiagonlizableExplain[U2[[#]],0],{" in \[DoubleStruckCapitalC]\n"}],{}]&/@Range[5])]]


cDiagonlizableExplain[m_,p_Integer]:=If[m=={},{},Module[{m1=MatrixForm[m],Eigen=cEigensystem[m,p],\[Lambda]s,bs,\[Lambda]M,bM},
\[Lambda]s=If[Eigen[[1]]=={},{{}},DiagonalMatrix[Eigen[[1]]]];
bs=Eigen[[2]];
\[Lambda]M=If[Eigen[[1]]=={},{{}},MatrixForm[DiagonalMatrix[Eigen[[1]]]]];
bM=MatrixForm[Eigen[[2]]];
Switch[cDiagonlizableTest[m,p],
1,{m1,"\[NotEqual]",bM,\[Lambda]M,Superscript[bM,"-1"],"no enough eigenvalues"},
2,{m1,"\[NotEqual]",bM,\[Lambda]M,Superscript[bM,"-1"],"no enough eigenvectors"},
3,{m1,"\[NotEqual]",bM,\[Lambda]M,Superscript[bM,"-1"],"eigenvectors is not invertible"},
4,{m1,"=",bM,\[Lambda]M,Superscript[bM,"-1"],"by non-unitary"},
5,{m1,"=",bM,\[Lambda]M,Superscript[bM,"-1"],"by unitary"}]]]
Row[cDiagonlizableExplain[IdentityMatrix[2],3]]
Row[cDiagonlizableExplain[\!\(\*
TagBox[
RowBox[{"(", GridBox[{
{
RowBox[{"-", "1"}], 
RowBox[{"-", "1"}]},
{
RowBox[{"-", "1"}], "0"}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}}], ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\) ,3]]


cDiagonlizableCount[UG_,meaning_,p_Integer]:=
Module[{
U1={0,0,0,0,0},
U2={{},{},{},{},{}},
output={"Number of no enough eigenvalues: ","Number of no enough eigenvectors: ","Number of eigenvectors not invertible: ","Number of non-unitary diagonalizable: ","Number of unitary diagonalizable: "}},
If[Head/@UG=={Function,Integer},
Module[{d=UG[[2]],Tc,A,stack={1}},
Tc=Tuples[cBasis[p],d];
While[Length[stack]>0,
If[Length[stack]<d,
If[stack[[-1]]>Length[Tc],
If[Length[stack]<=1,Break[],stack=stack[[1;;-2]];stack[[-1]]++]];
AppendTo[stack,1],
If[stack[[-1]]>Length[Tc],
If[Length[stack]<=1,Break[],stack=stack[[1;;-2]]],
A=Tc[[stack]];
If[UG[[1]][A],Module[{index=cDiagonlizableTest[A,p]},
U1[[index]]++;
If[U2[[index]]=={}\[Or]Max[Abs[A]]<Max[Abs[U2[[index]]]],U2[[index]]=A]]]];
stack[[-1]]++]]],
Module[{index=cDiagonlizableTest[#,p]},
U1[[index]]++;
If[U2[[index]]=={}\[Or]Max[Abs[#]]<Max[Abs[U2[[index]]]],U2[[index]]=#]]&/@UG];
Join[meaning,{", Total Number: ",Total[U1],"\n"},Join@@(If[U1[[#]]>0,Join[{output[[#]],U1[[#]],"\n"},cDiagonlizableExplain[U2[[#]],p],{" in \!\(\*SubscriptBox[\(\[DoubleStruckCapitalF]\), SuperscriptBox[\(p\), \(2\)]]\)\n"},cDiagonlizableExplain[U2[[#]],0],{" in \[DoubleStruckCapitalC]\n"}],{}]&/@Range[5])]]
cUnitaryCount[p_Integer,d_Integer]:=cDiagonlizableCount[cUnitaryGroup[p,d],{"When d=",d,", p=",p,", unitary"},p]
cUnitaryCount[p_Integer,d_Integer,_]:=cDiagonlizableCount[{cMod[#\[ConjugateTranspose].#,p]==IdentityMatrix[d]&,d},{"When d=",d,", p=",p,", unitary."},p]
Row[cUnitaryCount[3,2]]


(* ::Text:: *)
(*Print @@ cUnitaryCount[7, 2]*)
(*Print @@ cUnitaryCount[3, 3]*)


cUnitaryGroupCount[p_Integer,d_Integer]:=p^((d(d-1))/2) \!\(
\*SubsuperscriptBox[\(\[Product]\), \(j = 1\), \(d\)]\((
\*SuperscriptBox[\(p\), \(j\)] - 
\*SuperscriptBox[\((\(-1\))\), \(j\)])\)\)
cUnitaryGroupCount[3,2]


(* ::Text:: *)
(*Test when \[ScriptCapitalU](Subscript[t, 0]+\[DifferentialD]t,Subscript[t, 0])=1-I \[CapitalOmega] \[DifferentialD]t, \[DifferentialD]t=1, whether it is possible to have \[CapitalOmega]\[ConjugateTranspose]==\[CapitalOmega]...*)
(*It seems the result is that only strange \[ScriptCapitalU] may have this result...*)


Column[Row[cDiagonlizableExplain[#,3]]&/@Select[cUnitaryGroup[3,2],#\[ConjugateTranspose]==#&[cMod[(IdentityMatrix[2]-#)cPower[I,-1,3],3]]&]]


(* ::Section:: *)
(*Gleason's Theorem*)


cNonZeroNormVectors::usage"Non-Zero-Norm Vectors";
cNonZeroNormVectors[p_Integer,d_Integer]:=cNonZeroNormVectors[p,d] =Select[Tuples[cBasis[p],d],cMod[#\[Conjugate].#,p]!=0&]
Length[cNonZeroNormVectors[3,2]]


cNonZeroNormVectorsRepresentative[p_Integer,d_Integer]:=cNonZeroNormVectorsRepresentative[p,d]=cVectors2Representative[#,p]&/@cUnitNormVectorsRepresentative[p,d]
cNonZeroNormVectorsRepresentative[3,2]


(*http://en.wikipedia.org/wiki/Disjoint-set_data_structure*)
makeSet[X_List]:=Module[{find,union,parent,x,rank},
Do[parent[x]=x;rank[x]=0,{x,X}];
find[x_]:=Module[{},If[parent[x]!=x,parent[x]=find[parent[x]]];parent[x]];
union[x_,y_]:=Module[{xRoot:=find[x],yRoot:=find[y]},
If[xRoot!=yRoot,
Which[
rank[xRoot]<rank[yRoot],parent[xRoot]=yRoot,
rank[xRoot]>rank[yRoot],parent[yRoot]=xRoot,
True,parent[yRoot]=xRoot;rank[xRoot]=rank[xRoot]+1]]];
{X,find,union}]
combineGroupOrbits[G_List,X_List,f_]:=Module[{x,g,union=X[[3]]},Do[union[f[g,x],x],{g,G},{x,X[[1]]}];X]
Module[{X=combineGroupOrbits[cUnitCirle[3],makeSet[cUnitNormVectors[3,2]],cMod[#1 #2,3]&]},GatherBy[X[[1]],X[[2]]]]


cStateOrder:={StringLength[ToString[#]]&,#\[Conjugate].#&}


cAngleEndStates[p_Integer,d_Integer,start\[CapitalPsi]_List]:=cAngleEndStates[p,d,start\[CapitalPsi]]=
Module[{angles=makeSet[cNonZeroNormVectorsRepresentative[p,d]]},
angles=Switch[start\[CapitalPsi],
UnitVector[d,1],
combineGroupOrbits[cUnitaryGroup[p,d-1],angles,cVectors2Representative[Prepend[cMod[#1.Rest[#2],p],First[#2]],p]&],
UnitVector[d,d],
combineGroupOrbits[cUnitaryGroup[p,d-1],angles,cVectors2Representative[Append[cMod[#1.Most[#2],p],Last[#2]],p]&],
_,
Dialog[]];
SortBy[#,cStateOrder]&/@GatherBy[angles[[1]],angles[[2]]]]
cAngleEndStates[p_Integer,d_Integer]:=cAngleEndStates[p,d]=cAngleEndStates[p,d,UnitVector[d,1]]
Length[cAngleEndStates[3,2]]


cAngles[p_Integer,d_Integer,start\[CapitalPsi]_List]:=cAngles[p,d,start\[CapitalPsi]]=Map[{start\[CapitalPsi],#}&,cAngleEndStates[p,d,start\[CapitalPsi]],{2}]
cAngles[p_Integer,d_Integer]:=cAngles[p,d]=cAngles[p,d,UnitVector[d,1]]
Map[MatrixForm[#\[Transpose]]&,cAngles[3,2],{2}]
Length[cAngles[7,2]]
Length[cAngles[11,2]]
Length[cAngles[3,3]]


perpendicularState::usage="Find a state perpendicular to \[CapitalPsi] on the plane span by \[CapitalPsi] and \[CapitalPhi].";perpendicularState[\[CapitalPsi]_List,\[CapitalPhi]_List,p_Integer]:=cMod[\[CapitalPhi](\[CapitalPsi]\[Conjugate].\[CapitalPsi])-\[CapitalPsi](\[CapitalPsi]\[Conjugate].\[CapitalPhi]),p]
perpendicularState[{1,0,1},{1,1,0},3]
perpendicularState[{1,1,0},{1,0,1},3]


(* ::Text:: *)
(*Move (an angle from start\[CapitalPsi] to end\[CapitalPsi]) to (an angle from start\[CapitalPhi] to endState)*)


endState[start\[CapitalPsi]_List,start\[CapitalPhi]_List,p_Integer][end\[CapitalPsi]_List]:=
Module[{
start\[CapitalPsi]Normal=cNormalize[start\[CapitalPsi],p],
start\[CapitalPhi]Normal=cNormalize[start\[CapitalPhi],p],
start\[CapitalPsi]Perp=cNormalize[perpendicularState[start\[CapitalPsi],start\[CapitalPhi],p],p],
d=Length[start\[CapitalPsi]]},
Which[start\[CapitalPsi]Perp==ConstantArray[0,d],
(*If \[VerticalSeparator]start\[CapitalPsi]\[RightAngleBracket] \[DoubleVerticalBar] \[VerticalSeparator]start\[CapitalPhi]\[RightAngleBracket], then we don't have to move the angle.*)end\[CapitalPsi],
cMod[start\[CapitalPsi]Perp\[Conjugate].start\[CapitalPsi]Perp,p]!=0,
(*If start\[CapitalPsi]PerpNorm\[NotEqual]0, we can use \[VerticalSeparator]endState\[RightAngleBracket]\[Equal]\[VerticalSeparator]end\[CapitalPsi]\[RightAngleBracket]-\[Alpha]\[LeftDoubleBracket]1\[RightDoubleBracket]\[VerticalSeparator]start\[CapitalPsi]\[RightAngleBracket]-\[Alpha]\[LeftDoubleBracket]2\[RightDoubleBracket]\[VerticalSeparator]start\[CapitalPsi]Perp\[RightAngleBracket]+\[Alpha]\[LeftDoubleBracket]1\[RightDoubleBracket]\[VerticalSeparator]start\[CapitalPhi]\[RightAngleBracket]+\[Alpha]\[LeftDoubleBracket]2\[RightDoubleBracket]\[VerticalSeparator]start\[CapitalPhi]Perp\[RightAngleBracket], where \[Alpha]\[LeftDoubleBracket]1\[RightDoubleBracket]\[VerticalSeparator]start\[CapitalPsi]\[RightAngleBracket]-\[Alpha]\[LeftDoubleBracket]2\[RightDoubleBracket]\[VerticalSeparator]start\[CapitalPsi]Perp\[RightAngleBracket] is the projection from \[VerticalSeparator]end\[CapitalPsi]\[RightAngleBracket].*)
Module[{
start\[CapitalPhi]Perp=cNormalize[perpendicularState[start\[CapitalPhi],start\[CapitalPsi],p],p],\[Alpha]=cMod[{start\[CapitalPsi]Normal\[Conjugate],start\[CapitalPsi]Perp\[Conjugate]}.end\[CapitalPsi],p]},cMod[end\[CapitalPsi]-\[Alpha].{start\[CapitalPsi]Normal,start\[CapitalPsi]Perp}+\[Alpha].{start\[CapitalPhi]Normal,start\[CapitalPhi]Perp},p]],
True,
(*If start\[CapitalPsi]PerpNorm\[Equal]0, we have to rotation the angle in higher dimension. It's hrad to determine the exact dimension, so we rotate them in the whole space.*)
Module[{
basis\[CapitalPsi]=cOrthogonalize[Prepend[IdentityMatrix[d],start\[CapitalPsi]Normal],p],basis\[CapitalPhi]=cOrthogonalize[Prepend[IdentityMatrix[d],start\[CapitalPhi]Normal],p]},
cMod[(basis\[CapitalPsi]\[Conjugate].end\[CapitalPsi]).basis\[CapitalPhi],p]]]]
endState[{-3-3 I,-3-3 I},{1,0},7][{1,0}]
endState[{-3-3 I,-3-3 I},{1,0},7][{0,1}]
endState[{-3-3 I,-3-3 I},{1,0},7][{-3-3 I,-3-3 I}]
cMod[(-3-3 I)endState[{-3-3 I,-3-3 I},{1,0},7][{1,0}]+(-3-3 I)endState[{-3-3 I,-3-3 I},{1,0},7][{0,1}],7]


endState[{1,1,1+I},{0,0,1},3][{1,0,0}]
Position[cAngleEndStates[3,3,{0,0,1}],cVectors2Representative[endState[{1,1,1+I},{0,0,1},3][{1,0,0}],3]]
Position[cAngleEndStates[3,3,{0,0,1}],{1,1+I,1}]


cVectors2Representative[endState[{1,2+I},{0,1},7][{0,1}],7]
Position[cAngleEndStates[7,2,{0,1}],cVectors2Representative[endState[{1,2+I},{0,1},7][{0,1}],7]]
Position[cAngleEndStates[7,2,{0,1}],{1,2+I}]


cVectors2Representative[endState[{1,2+2I},{0,1},11][{1,0}],11]
Position[cAngleEndStates[11,2,{0,1}],cVectors2Representative[endState[{1,2+2I},{0,1},11][{1,0}],11]]
Position[cAngleEndStates[11,2,{0,1}],{1,3+3I}]


(* ::Text:: *)
(*endStatesOfStandardBasis[start\[CapitalPsi]_List,p_Integer]:=endState[start\[CapitalPsi],UnitVector[d,1],p_Integer]/@IdentityMatrix[d]*)
(*Simplify the computation, and comments.*)
(**)
(*The original promise of this function is the following claim.*)
(*Claim: If {\[VerticalSeparator]Subscript[\[CapitalPsi], 1]\[RightAngleBracket],\[VerticalSeparator]Subscript[\[CapitalPsi], 2]\[RightAngleBracket],...,\[VerticalSeparator]Subscript[\[CapitalPsi], d]\[RightAngleBracket]}==endStatesOfStandardBasis[start\[CapitalPsi],p], then {\[Pi](\[VerticalSeparator]start\[CapitalPsi]\[RightAngleBracket],\[VerticalSeparator]Subscript[e, 1]\[RightAngleBracket]),\[Pi](\[VerticalSeparator]start\[CapitalPsi]\[RightAngleBracket],\[VerticalSeparator]Subscript[e, 2]\[RightAngleBracket]),...,\[Pi](\[VerticalSeparator]start\[CapitalPsi]\[RightAngleBracket],\[VerticalSeparator]Subscript[e, d]\[RightAngleBracket])}=={\[Pi](\[VerticalSeparator]Subscript[e, 1]\[RightAngleBracket],\[VerticalSeparator]Subscript[\[CapitalPsi], 1]\[RightAngleBracket]),\[Pi](\[VerticalSeparator]Subscript[e, 1]\[RightAngleBracket],\[VerticalSeparator]Subscript[\[CapitalPsi], 2]\[RightAngleBracket]),...,\[Pi](\[VerticalSeparator]Subscript[e, 1]\[RightAngleBracket],\[VerticalSeparator]Subscript[\[CapitalPsi], d]\[RightAngleBracket])}*)
(*Notice that the {} above are sets instead of lists, i.e., we don't promise the order of sending. *)
(*In order to make sure the order of sending, we check cMod[pBasis\[Transpose].start\[CapitalPsi]Normal,p]==UnitVector[d,1] at the very end...*)


Needs["VectorAnalysis`"]
endStatesOfStandardBasis[start\[CapitalPsi]_List,p_Integer]:=
Module[{start\[CapitalPsi]Normal=cNormalize[start\[CapitalPsi],p],start\[CapitalPsi]Perp,d=Length[start\[CapitalPsi]],start\[CapitalPsi]3,basis},
start\[CapitalPsi]Perp=cNormalize[UnitVector[d,1]-start\[CapitalPsi]Normal First[start\[CapitalPsi]Normal\[Conjugate]],p];
basis=Which[
start\[CapitalPsi]Perp==ConstantArray[0,d],
IdentityMatrix[d],
cMod[start\[CapitalPsi]Perp\[Conjugate].start\[CapitalPsi]Perp,p]!=0,
start\[CapitalPhi]Perp=cNormalize[start\[CapitalPsi]Normal-UnitVector[d,1]First[start\[CapitalPsi]Normal],p];
(*cMod[end\[CapitalPsi]+({start\[CapitalPsi]Normal\[Conjugate],start\[CapitalPsi]Perp\[Conjugate]}.end\[CapitalPsi]).{UnitVector[d,1]-start\[CapitalPsi]Normal,start\[CapitalPhi]Perp-start\[CapitalPsi]Perp},p]*)
cMod[IdentityMatrix[d]+{start\[CapitalPsi]Normal,start\[CapitalPsi]Perp}\[ConjugateTranspose].{UnitVector[d,1]-start\[CapitalPsi]Normal,start\[CapitalPhi]Perp-start\[CapitalPsi]Perp},p],
Length[start\[CapitalPsi]]==3,
If[Do[
start\[CapitalPsi]Perp=cNormalize[cMod[\[CapitalPhi]-start\[CapitalPsi]Normal(start\[CapitalPsi]Normal\[Conjugate].\[CapitalPhi]),p],p];
If[cMod[start\[CapitalPsi]Perp\[Conjugate].start\[CapitalPsi]Perp,p]==0,Continue[]];
start\[CapitalPsi]3=cMod[CrossProduct[start\[CapitalPsi]Normal,start\[CapitalPsi]Perp]\[Conjugate],p];
If[cMod[start\[CapitalPsi]3\[Conjugate].start\[CapitalPsi]3,p]==0,Continue[]];
Return[{}],
{\[CapitalPhi],cUnitNormVectorsRepresentative[p,d]}]===Null,
cOrthogonalize[Prepend[IdentityMatrix[d],start\[CapitalPsi]Normal],p],
{start\[CapitalPsi]Normal,start\[CapitalPsi]Perp,start\[CapitalPsi]3}]\[ConjugateTranspose],
True,
(*{basis\[CapitalPsi]\[Conjugate].{1,0,...,0},basis\[CapitalPsi]\[Conjugate].{0,1,...,0},...,basis\[CapitalPsi]\[Conjugate].{0,0,...,1}}
\[Equal]{basis\[CapitalPsi]\[Conjugate]\[LeftDoubleBracket];;,1\[RightDoubleBracket],basis\[CapitalPsi]\[Conjugate]\[LeftDoubleBracket];;,2\[RightDoubleBracket],...,basis\[CapitalPsi]\[Conjugate]\[LeftDoubleBracket];;,d\[RightDoubleBracket]}
\[Equal](basis\[CapitalPsi]\[Conjugate])\[Transpose]\[Equal]basis\[CapitalPsi]\[ConjugateTranspose]*)
cOrthogonalize[Prepend[IdentityMatrix[d],start\[CapitalPsi]Normal],p]\[ConjugateTranspose]];
If[#===Null,Dialog[],#]&[
Do[
Which[
cMod[pBasis\[Transpose].start\[CapitalPsi]Normal,p]==UnitVector[d,1],Return[pBasis],
cMod[pBasis\[ConjugateTranspose].start\[CapitalPsi]Normal,p]==UnitVector[d,1],Return[pBasis\[Conjugate]]],
{pBasis,Permutations[basis]}]]]
endStatesOfStandardBasis[{-3-3 I,-3-3 I},7]


endStatesOfStandardBasis[{1,1,1+I},3]
Position[cAngleEndStates[3,3],cVectors2Representative[#,3]]&/@endStatesOfStandardBasis[{1,1,1+I},3]
cMod[endStatesOfStandardBasis[{1,1,1+I},3]\[Transpose].Prepend[IdentityMatrix[3],{1,1,1+I}]\[Transpose],3]//MatrixForm


endStatesOfStandardBasis[{0,0,1},3]
Position[cAngleEndStates[3,3],cVectors2Representative[#,3]]&/@endStatesOfStandardBasis[{0,0,1},3]
cMod[endStatesOfStandardBasis[{0,0,1},3]\[Transpose].Prepend[IdentityMatrix[3],{0,0,1}]\[Transpose],3]//MatrixForm


cNormalize[{0,1,1},3]
endStatesOfStandardBasis[{0,1,1},3]
Position[cAngleEndStates[3,3],cVectors2Representative[#,3]]&/@endStatesOfStandardBasis[{0,1,1},3]
cMod[endStatesOfStandardBasis[{0,1,1},3]\[Transpose].Prepend[IdentityMatrix[3],cNormalize[{0,1,1},3]]\[Transpose],3]//MatrixForm


endStatesOfStandardBasis[{-3-3 I,-3-3 I},7]
Position[cAngleEndStates[7,2],cVectors2Representative[#,7]]&/@endStatesOfStandardBasis[{-3-3 I,-3-3 I},7]
cMod[endStatesOfStandardBasis[{-3-3 I,-3-3 I},7]\[Transpose].Prepend[IdentityMatrix[2],{-3-3 I,-3-3 I}]\[Transpose],7]//MatrixForm


endStatesOfStandardBasis[{0,1},11]
Position[cAngleEndStates[11,2],cVectors2Representative[#,11]]&/@endStatesOfStandardBasis[{0,1},11]
cMod[endStatesOfStandardBasis[{0,1},11]\[Transpose].Prepend[IdentityMatrix[2],{0,1}]\[Transpose],11]//MatrixForm


(* ::Text:: *)
(*Compute the quotient of two numbers in Subscript[\[DoubleStruckCapitalF], p^2]. In fact, given two number m\[Element]Subscript[\[DoubleStruckCapitalF], p^2] and n\[Element]Subscript[\[DoubleStruckCapitalF], p^2], this function return all solutions x of m==n x (mod p). In particular, Indeterminate is a solution when n==0. We can think we are actually solving m==n x (mod p) in the discrete complex projective plane Subscript[\[DoubleStruckCapitalP]\[DoubleStruckCapitalF], p^2].*)


cQuotient[m_?(ArrayDepth[#]<=0&),n_?(ArrayDepth[#]<=0&),p_Integer]:=cQuotient[m,n,p]=If[cMod[n,p]==0,Append[#,Indeterminate],#]&[Select[cBasis[p],cMod[m-n #,p]==0&]]
cQuotient[0,0,3]


(* ::Text:: *)
(*Compute the ratio between two states. In fact, given two states \[LeftBracketingBar]\[CapitalPsi]\[RightAngleBracket] and \[LeftBracketingBar]\[CapitalPhi]\[RightAngleBracket] over Subscript[\[DoubleStruckCapitalF], p^2], this function return all solutions x of \[LeftBracketingBar]\[CapitalPhi]\[RightAngleBracket]==x\[LeftBracketingBar]\[CapitalPsi]\[RightAngleBracket] (mod p). In particular, Indeterminate is a solution when \[LeftBracketingBar]\[CapitalPsi]\[RightAngleBracket]==0. We can think we are actually solving \[LeftBracketingBar]\[CapitalPhi]\[RightAngleBracket]==x\[LeftBracketingBar]\[CapitalPsi]\[RightAngleBracket] (mod p) in the discrete complex projective plane Subscript[\[DoubleStruckCapitalP]\[DoubleStruckCapitalF], p^2].*)


cQuotient[\[CapitalPhi]_List,\[CapitalPsi]_List,p_Integer]:=Intersection@@MapThread[cQuotient[#1,#2,p]&,{\[CapitalPhi],\[CapitalPsi]}]


(* ::Section:: *)
(*Gleason's Theorem without identifying angles and solve as group*)


cRowReduceForModuleOverEuclideanDomain[A_List,N_]:=cRowReduceForModuleOverEuclideanDomain[A,N]=
Module[{a=A,Col,iMin,vMin,nonZeroCount,Row1=1},
For[Col=1,Col<=Dimensions[a][[2]],
(*Find pivot for column k:*)
vMin=\[Infinity];
nonZeroCount=0;
Do[If[a[[i,Col]]!=0,
nonZeroCount++;
If[N[a[[i,Col]]]<vMin,
vMin=N[a[[i,Col]]];
iMin=i]],
{i,Row1,Dimensions[a][[1]]}];

If[nonZeroCount==0,
Col++,
{a[[Row1]],a[[iMin]]}={a[[iMin]],a[[Row1]]};
a[[;;Row1-1,Col;;]]=a[[;;Row1-1,Col;;]]-KroneckerProduct[Quotient[a[[;;Row1-1,Col]],a[[Row1,Col]]],a[[Row1,Col;;]]];
If[nonZeroCount==1,
Col++;
Row1++;
If[Row1>Dimensions[a][[1]],Break[]],
(*Do for all rows below pivot:*)
(*Do for all remaining elements in current row:*)
(*'Fill lower triangular matrix with zeros:*)
a[[Row1+1;;,Col;;]]=a[[Row1+1;;,Col;;]]-KroneckerProduct[Quotient[a[[Row1+1;;,Col]],a[[Row1,Col]]],a[[Row1,Col;;]]]]]];
a[[;;Row1-1]]]
cRowReduceForModuleOverEuclideanDomain[{{2,1},{3,1}},Abs]//MatrixForm
cRowReduceForModuleOverEuclideanDomain[{{2,-4,2,-2},{2,-4,3,-4},{4,-8,3,-2},{0,0,-1,2}},Abs]//MatrixForm
cRowReduceForModuleOverEuclideanDomain[{{1,0,4},{2,0,3},{2,1,2}},Abs]//MatrixForm
cRowReduceForModuleOverEuclideanDomain[{{1,-2,1,-1},{2,-3,4,-3},{3,-5,5,-4},{-1,1,-3,2}},Abs]//MatrixForm
cRowReduceForModuleOverEuclideanDomain[{{1-I,1-I},{1-I,1-I}},Re[#]^2+Im[#]^2&]//MatrixForm


cRowReduceOver\[DoubleStruckCapitalZ][A_List]:=cRowReduceOver\[DoubleStruckCapitalZ][A]=
Module[{a=A,Col,iMin,vMin,nonZeroCount,Row1=1},
For[Col=1,Col<=Dimensions[a][[2]],
(*Find pivot for column k:*)
vMin=\[Infinity];
nonZeroCount=0;
Do[If[a[[i,Col]]!=0,
nonZeroCount++;
If[Abs[a[[i,Col]]]<vMin,
vMin=Abs[a[[i,Col]]];
iMin=i]],
{i,Row1,Dimensions[a][[1]]}];

If[nonZeroCount==0,
Col++,
{a[[Row1]],a[[iMin]]}={a[[iMin]],a[[Row1]]};
a[[Row1]]=a[[Row1]]/GCD@@a[[Row1]];
If[a[[Row1,Col]]==-1,a[[Row1]]=-a[[Row1]]];
a[[;;Row1-1,Col;;]]=a[[;;Row1-1,Col;;]]-KroneckerProduct[Quotient[a[[;;Row1-1,Col]],a[[Row1,Col]]],a[[Row1,Col;;]]];
If[nonZeroCount==1,
Col++;
Row1++;
If[Row1>Dimensions[a][[1]],Break[]],
(*Do for all rows below pivot:*)
(*Do for all remaining elements in current row:*)
(*'Fill lower triangular matrix with zeros:*)
a[[Row1+1;;,Col;;]]=a[[Row1+1;;,Col;;]]-KroneckerProduct[Quotient[a[[Row1+1;;,Col]],a[[Row1,Col]]],a[[Row1,Col;;]]]]]];
a[[;;Row1-1]]]
cRowReduceOver\[DoubleStruckCapitalZ][{{2,1},{3,1}}]//MatrixForm
cRowReduceOver\[DoubleStruckCapitalZ][{{2,-4,2,-2},{2,-4,3,-4},{4,-8,3,-2},{0,0,-1,2}}]//MatrixForm
cRowReduceOver\[DoubleStruckCapitalZ][{{1,0,4},{2,0,3},{2,1,2}}]//MatrixForm
cRowReduceOver\[DoubleStruckCapitalZ][{{1,-2,1,-1},{2,-3,4,-3},{3,-5,5,-4},{-1,1,-3,2}}]//MatrixForm


cOrthonormalBasis[p_Integer,d_Integer]:=cOrthonormalBasis[p,d]=Switch[d,
2,Table[{\[CapitalPsi],cNormalize[{-\[CapitalPsi][[2]]\[Conjugate],\[CapitalPsi][[1]]\[Conjugate]},p]},{\[CapitalPsi],cUnitNormVectorsRepresentative[p,d]}],
3,Module[{basises={},\[CapitalPsi]3},
Do[Do[
If[cMod[\[CapitalPsi]1\[Conjugate].\[CapitalPsi]2,p]==0,
\[CapitalPsi]3=cMod[CrossProduct[\[CapitalPsi]1,\[CapitalPsi]2]\[Conjugate],p];
If[cMod[\[CapitalPsi]3\[Conjugate].\[CapitalPsi]3,p]!=0,AppendTo[basises,{\[CapitalPsi]1,\[CapitalPsi]2,cNormalize[\[CapitalPsi]3,p]}]]],
{\[CapitalPsi]2,cUnitNormVectorsRepresentative[p,d]}],{\[CapitalPsi]1,cUnitNormVectorsRepresentative[p,d]}];
basises],
_,cOrthonormalBasisInSubspace[IdentityMatrix[d],p]]
cOrthonormalBasis[3,2]
Length[cOrthonormalBasis[3,3]]


cUnitNormVectorsRepresentative[3,2]


cGleasonMatrix[p_Integer,d_Integer]:=cGleasonMatrix[p,d]=
(*Switch[d,
2,
Module[{
unitNormVectors=cUnitNormVectorsRepresentative[p,d],
unitNormVectorsCount,unitNormVectorsi,row,row1},
unitNormVectorsCount=Length[unitNormVectors];
row1=UnitVector[unitNormVectorsCount+1,unitNormVectorsCount+1];
Table[
unitNormVectorsi=unitNormVectors\[LeftDoubleBracket]i\[RightDoubleBracket];
row=row1;
row\[LeftDoubleBracket]i\[RightDoubleBracket]++;
row\[LeftDoubleBracket]Position[unitNormVectors,cNormalize[{-unitNormVectorsi\[LeftDoubleBracket]2\[RightDoubleBracket]\[Conjugate],unitNormVectorsi\[LeftDoubleBracket]1\[RightDoubleBracket]\[Conjugate]},p]]\[LeftDoubleBracket]1,1\[RightDoubleBracket]\[RightDoubleBracket]++;
row,{i,unitNormVectorsCount}]],
_,*)Table[Append[Boole[MemberQ[basis,#]]&/@cUnitNormVectorsRepresentative[p,d],1],{basis,cOrthonormalBasis[p,d]}](*]*)
cGleasonMatrix[3,2]//MatrixForm
AbsoluteTiming[Dimensions[cGleasonMatrix[3,3]]]


cGleasonAbelianGroup[p_Integer,d_Integer]:=cRowReduceOver\[DoubleStruckCapitalZ][cGleasonMatrix[p,d]]
cGleasonAbelianGroup[3,2]//MatrixForm
AbsoluteTiming[Dimensions[cGleasonAbelianGroup[3,3]]]


cGleasonMatrixVerify[M_List,p_Integer,d_Integer]:=
Module[{\[CapitalPsi]s={}},Do[If[cMod[M.Append[Table[(\[CapitalPhi]\[Conjugate].\[CapitalPsi])(\[CapitalPsi]\[Conjugate].\[CapitalPhi]),{\[CapitalPhi],cUnitNormVectorsRepresentative[p,d]}],-1],p]!=ConstantArray[0,Length[M]],AppendTo[\[CapitalPsi]s,\[CapitalPsi]]],{\[CapitalPsi],cUnitNormVectorsRepresentative[p,d]}];\[CapitalPsi]s]
{cGleasonMatrixVerify[cGleasonMatrix[#,2],#,2],cGleasonMatrixVerify[cGleasonAbelianGroup[#,2],#,2]}&/@{3,7}
{cGleasonMatrixVerify[cGleasonMatrix[#,3],#,3],cGleasonMatrixVerify[cGleasonAbelianGroup[#,3],#,3]}&/@{3}


cPossibleZeroCount[p_Integer,d_Integer]:=Length[cUnitNormVectorsRepresentative[p,d]]-MatrixRank[cGleasonAbelianGroup[p,d]]
cPossibleZeroCount[3,2]


cMaxZeroCount[p_Integer,d_Integer]:=Length[Select[cUnitNormVectorsRepresentative[p,d],#[[1]]==0&]]
cMaxZeroCount[3,2]


cSolutionChar[p_Integer,d_Integer]:=Module[{len=Length[cGleasonAbelianGroup[p,d][[1]]],zeros},
zeros=ConstantArray[0,len];Do[If[cGleasonAbelianGroup[p,d][[row]]!=zeros,Return[If[cGleasonAbelianGroup[p,d][[row,;;-2]]==ConstantArray[0,len-1],cGleasonAbelianGroup[p,d][[row,-1]],0]]],{row,Length[cGleasonAbelianGroup[p,d]],1,-1}]]
cSolutionChar[3,2]
cSolutionChar[7,2]


cGleasonPrint[reducedForm_List,p_Integer,d_Integer]:=Module[{unitNormVectorsRepresentative=cUnitNormVectorsRepresentative[p,d],position,l,output={}},
l=Length[unitNormVectorsRepresentative];
Do[
position=Position[Most[row],Except[0],{1},Heads->False];
If[position=={},
If[Last[row]==0,Break[],AppendTo[output,\!\(TraditionalForm\`0 == Last[row]\)]],
AppendTo[output,
Row[Join[{\!\(TraditionalForm\`row[\([position[\([1, 1]\)]]\)] \[Pi]\ MatrixForm[unitNormVectorsRepresentative[\([position[\([1, 1]\)]]\)]]\)},Flatten[{Switch[row[[#[[1]]]],1,"\"+\"",-1,"\"-\"",_,NumberForm[row[[#[[1]]]],0,NumberSigns->{"\"-\"","\"+\""}]],\!\(TraditionalForm\`\[Pi]\ MatrixForm[unitNormVectorsRepresentative[\([#[\([1]\)]]\)]]\)}&/@Rest[position]],{"\"\[Equal]\"",Last[row]}]]]],
{row,reducedForm}];
output]
Column[cGleasonPrint[cGleasonAbelianGroup[3,2],3,2]]


cInformationlessMatrix[n_Integer]:=ArrayFlatten[{{IdentityMatrix[n],ConstantArray[{1/3},n]}}]
cInformationlessMatrix[2]//MatrixForm


Module[{p=19},
Print[AbsoluteTiming[Dimensions[cGleasonMatrix[p,3]]]];
Print[AbsoluteTiming[cGleasonMatrixVerify[cGleasonMatrix[p,3],p,3]]];
Print[AbsoluteTiming[cGleasonMatrixVerify[cGleasonAbelianGroup[p,3],p,3]]];
Print[AbsoluteTiming[cSolutionChar[p,3]]];
Print[AbsoluteTiming[MatrixRank[cGleasonAbelianGroup[p,3]]]];
Print[AbsoluteTiming[cPossibleZeroCount[p,3]]];
Print[AbsoluteTiming[cMaxZeroCount[p,3]]];
Print[Column[cGleasonPrint[cGleasonAbelianGroup[p,3],p,3]]]];
Print[];
