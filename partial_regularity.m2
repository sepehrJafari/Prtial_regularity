restart

loadPackage "EdgeIdeals"



---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- the following is our tool kit (tool kit is a set of costume made 
--that I need regardless of the problem)
list1= flatten goodList
ommitNull = list1 ->(
    flatten for i  to length list1-1 list (
	if list1_i!={} then list1_i else continue
	)    
    )



---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- this gives the multi-degree resolution
--the entries are an ideal and its ring
-- the out put is the degree shifts and homological degrees
-- note that this function does not give the betti numbers as an output

mRes = (ideal1,RING) -> (
    module1 = trim  ideal1*RING^1;
    homologicalDegree=0;
    outPut={};
    while module1!=0 do (
    	ge :=  mingens (module1);
    	col:=numgens source ge;
    	l:= unique for j to col -1 list {homologicalDegree+1,degree ge_j };
    	outPut=outPut|l;
    	homologicalDegree=homologicalDegree+1;
    	module1 = trim image syz generators  module1;
    	);
    return outPut
    )

-- the following takes a multi-res in the above format and degree as an entry
-- the out put is the partial degree with respect to given degree
-- Note that the output is the partial regualrity of the qoutiont ring

parReg = (multiRes,deg)  -> (
    max for i to length multiRes -1 list(
	 multiRes_i_1_deg-multiRes_i_0
	)
    )


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- this function gives a random sample of bipartite graphs.

samGraph = (RING , lowerBound , upperBound, samSize) -> (
    counter:= 0;
    t:=0;
    list1 := while counter<samSize list (
	print(counter,t);
	t=t+1;
    	graph  := randomGraph(RING,random(lowerBound,upperBound));
    	if isBipartite(graph) then (graph, counter = counter +1) else continue
    	);
    list1 = for i to length list1 -1 list list1_i_0;
    return  list1
    )



---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- this function gives a random sample of co-chordal graphs.


samGraph = (RING , lowerBound , upperBound, samSize) -> (
    counter:= 0;
    t:=0;
    list1 := while counter<samSize list (
	print(counter,t);
	t=t+1;
    	graph  := randomGraph(RING,random(lowerBound,upperBound));
    	if regularity (edgeIdeal graph)==2 then (graph, counter = counter +1) else continue
    	);
    list1 = for i to length list1 -1 list list1_i_0;
    return  list1
    )


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- let R be a subring of S with fewer variables. In the following we find a way to 
-- intruduce the ideals of R to S

xNum=20

S = QQ[x_1..x_(xNum),T_1,T_2,Degrees=>{xNum:{1,0,0},{0,1,0},{0,0,1}}];

(R,f) = selectVariables({0..xNum-1},S)

--sub(I,S) this could be an alternative solution. Search for it if needed.


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- in the following block we claculate partial reg for sum of ideals co-chordal graphs

restart

loadPackage "EdgeIdeals"

-- this function gives the varibles of any monomial.
-- the entries are monomials

xNum=20

monvars = (mon,RING) -> ( 
    var = first entries vars RING;
    flatten for i  to length var -1 list (
       	while mon % var_i ==0 list 
	i+1
	do 
	mon=mon//var_i
	)
    )


S = QQ[x_1..x_(xNum),T,Degrees=>{xNum:{1,0},{0,1}}];

(S1,f) = selectVariables({0..xNum-1},S)

graphList=samGraph(S1,7,10,10);

idealList= unique for i to length graphList -1 list f(edgeIdeal graphList_i);

I=idealList_0
J=idealList_6

genI = first entries gens I
genJ = first entries gens J
genIJ= first entries gens (I+J)

indYI= for i to length genI -1 list(monvars(genI_i,S))
indYJ= for i to length genJ -1 list(monvars(genJ_i,S))
indY= for i to length genIJ -1 list(monvars(genIJ_i,S))

xvars=first entries f(vars S1)
yvarsI = for i to length indYI -1 list (Y_(indYI_i))
yvarsJ = for i to length indYJ -1 list (Y_(indYJ_i))
yvars = for i to length indY -1 list (Y_(indY_i))

R=QQ[X_1..X_(xNum),yvars,Degrees=>{xNum:{1,0},length yvars:{0,1}}]
(R1,g1) = selectVariables(toList (0..(xNum+length yvarsI-1)),R)
(R2,g2) = selectVariables(toList(0..xNum-1)|toList(xNum+length yvarsI..(xNum + length yvarsI + length yvarsJ-1)),R)

genAlg= xvars|T*genIJ
genAlgI= xvars|(T*genI)
genAlgJ= xvars|(T*genJ)

rees = map(S,R,genAlg)
reesI = map(S,R1,genAlgI)
reesJ = map(S,R2,genAlgJ)

reesKer = trim ker rees;
reesKerI = g1(trim  ker reesI);
reesKerJ = g2(trim  ker reesJ);

reesKer
reesKerI
reesKerJ

peek betti res reesKer

I=f(ideal(x_7*x_8,x_6*x_13,x_7*x_13,x_11*x_13,x_7*x_15,x_7*x_19))

I=I+f(ideal(x_8*x_11,
	x_13*x_15,x_13*x_19,
	x_8*x_19,
       	x_7*x_11,
	x_6*x_11
	))
J=f(ideal(x_1*x_7,x_5*x_7, x_1*x_8,x_1*x_12,x_7*x_13,x_1*x_16,x_7*x_19))
J=f(ideal(x_4*x_6,x_4*x_8,x_6*x_8))



regularity I
regularity J
regularity (I+J)

gbase=trim ideal gens gb reesKer
l= first entries gens gbase
for i to length l-1 do (print (degree l_i))
for i to length l -1 do (if degree l_i == {2, 1} then (print (l_i);print("=========================")))

l_36
length l

peek betti res reesKer
