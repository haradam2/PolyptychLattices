needsPackage "SimplicialComplexes"
needsPackage "NormalToricVarieties"
needsPackage "Polyhedra"

--defining the Polyptych pair data type--

PolyptychPair = new Type of HashTable
expression PolyptychPair := P -> (expression polyptychPair)

-*
PolyptychLattice = new Type of HashTable
expression PolyptychLattice := P -> (expression polyptychLattice)
*-

--This is a comment to test the version control--

polyptychPair = method()
polyptychPair (Matrix, List, List):= PolyptychPair => (D, deltaN, deltaM) -> (
    new PolyptychPair from { 
        symbol Diagram => D,
        symbol RowComplex => deltaN, 
        symbol ColumnComplex => deltaM,
        symbol cache => new CacheTable from {
            symbol RowCharts => new MutableHashTable,
            symbol ColumnCharts => new MutableHashTable,
        }
        }
)

toricChart = method()
toricChart(Matrix, List, List) := (D, cols, maxFaces) -> (
    chartRays := entries submatrix(D, cols);
    normalToricVariety(chartRays, maxFaces)
)
toricChart(PolyptychPair, List, Nothing) := (P, rowFace, null) -> (
    P.cache.RowCharts#rowFace ??= toricChart(transpose P.Diagram, rowFace, P.ColumnComplex)
)
toricChart(PolyptychPair, Nothing, List) := (P, null, columnFace) -> (
    P.cache.ColumnCharts#columnFace ??= toricChart(P.Diagram, columnFace, P.RowComplex)
)

maxFaces = method()
maxFaces(SimplicialComplex) := (S) -> apply(facets(S), indices)

isPLPairSmooth = method()
isPLPairSmooth(Matrix, List, List) := (D, deltaN, deltaM) -> (
    --Checks smootheness of all toric charts
    minorDets := flatten table(deltaN, deltaM, 
        (n,m) -> det(submatrix(D,n,m)));
    all(minorDets, i -> (i == 1) or (i == -1))
)

areRaysConvex = method()
areRaysConvex(Matrix,List,List) := (describer, cols, simpcomp) -> (
    V := toricChart(describer, cols, simpcomp);
    
    divs := entries transpose submatrix'(describer, , cols);

    all for div in divs list (
        divisor := toricDivisor(div, V);
        checkresult := isNef(-divisor)
    ) do (
        if not checkresult then (
            print("failed axiom 3, the divisor ", toString div, 
                " is not nef on toric chart with rays ", rays V);
        )
    )
)

isCompleteToricVariety = method()
isCompleteToricVariety(Matrix, List, List) := (describer, cols, simpcomp) -> (
    V := toricChart(describer, cols, simpcomp);
    isComplete(V)
    --if not isComplete(V) then print("the toric chart with rays ",
    --    rays V, " is not complete");
)

isPolyptychPair = method()
isPolyptychPair(Matrix, List, List) := (D,deltaN,deltaM) -> (
    checksN :=all flatten for facit in deltaN list(
        {isCompleteToricVariety(transpose D,facit,deltaM),
        areRaysConvex(transpose D,facit,deltaM)}
    );
    checksM :=all flatten for facit in deltaM list(
        {isCompleteToricVariety(D,facit,deltaN),
        areRaysConvex(D,facit,deltaN)}
    );
    
    all flatten {checksM,checksN,isPLPairSmooth(D,deltaN,deltaM)}
)
isPolyptychPair(Matrix, SimplicialComplex, SimplicialComplex) := (D,deltaN,deltaM) -> (
    facitsN := maxFaces(deltaN);
    facitsM := maxFaces(deltaM);

    checksN :=all flatten for facit in facitsN list(
        {isCompleteToricVariety(transpose D,facit,facitsM),
        areRaysConvex(transpose D,facit,facitsM)}
    );
    checksM :=all flatten for facit in facitsM list(
        {isCompleteToricVariety(D,facit,facitsN),
        areRaysConvex(D,facit,facitsN)}
    );
    
    all flatten {checksM,checksN,isPLPairSmooth(D,facitsN,facitsM)}
)


--Main Example Initialization: MAKE SURE TO DELETE, they cant know we live here--

R = QQ[a..e]

D = matrix{{-1,0,1,0,-1},{0,1,0,-1,-1},{1,0,-1,-1,0},{0,-1,-1,0,1},{-1,-1,0,1,0}}
deltaN = simplicialComplex {a*b, b*c, c*d, d*e, e*a}
deltaM = simplicialComplex {a*b, b*c, c*d, d*e, e*a}

end--
restart
load "PLDataTypeAndWellDefinedCheck.m2"

--new check--

P = polyptychPair(D,maxFaces(deltaN),maxFaces(deltaM))

toricChart(P, {1,2}, )

peek P.cache.RowCharts

isWellDefined toricChart(P,,{1,2})

-*
Check
*-

R = QQ[a..e]

D = matrix{{-1,0,1,0,-1},{0,1,0,-1,-1},{1,0,-1,-1,0},{0,-1,-1,0,1},{-1,-1,0,1,0}}
deltaN = simplicialComplex {a*b, b*c, c*d, d*e, e*a}
deltaM = simplicialComplex {a*b, b*c, c*d, d*e, e*a}

facets(deltaN)


isPolyptychPair(D,maxFaces(deltaN),maxFaces(deltaM))

isPolyptychPair(D,deltaN,deltaM)

axiom1(D,maxFaces(deltaN),maxFaces(deltaM))

--New Example--

R = QQ[a..e]
deltaN = simplicialComplex {a*b, b*c, c*d, d*e, e*a}

maxFaces(deltaN)

--New Check--

R = QQ[a..e]

D = matrix{{-1,0,1,0,-1},{0,1,0,-1,-1},{1,0,-1,-1,0},{0,-1,-1,0,1},{-1,-1,0,1,0}}

deltaN = simplicialComplex {a*b, b*c, c*d, d*e, e*a}

areRaysConvex(D,{1,2},maxFaces(deltaN))

-- 
-- Checking Megumi's suggestion

-- 4x5

L = {-1, 1}
mats = flatten flatten flatten apply(L, i1 -> apply(L, i2 -> apply(L, i3 -> apply(L, i4 -> matrix({{0,1,0,-1, i1},{1,0,-1,0, i2},{0,-1,0,1, i3},{-1,0,1,0, i4}})))))

R = QQ[a..e]
N = simplicialComplex({a,b,c,d,a*b,b*c,c*d,d*a})
M = simplicialComplex ({a, b, c, d, e, a*b, b*c, c*d, d*e, e*a})

potentialPLs = apply(mats, i -> (i,M,N))
apply(potentialPLs, i -> isPolyptychPair i)

select(potentialPLs, i -> isPolyptychPair(i)==true)
-- have some true here

-- 5x6

L = {-1, 1}
mats = flatten flatten flatten flatten apply({-1, 0, 1}, i1 -> apply(L, i2 -> apply(L, i3 -> apply(L, i4 -> apply(L, i5 -> matrix({{-1, 0, 1, 0, -1, i1},{0, 1, 0, -1, -1, i2},{1, 0, -1, -1, 0, i3},{0, -1, -1, 0, 1, i4},{-1, -1, 0, 1, 0, i5}}))))))

R = QQ[a..f]
N = simplicialComplex ({a, b, c, d, e, a*b, b*c, c*d, d*e, e*a})
M = simplicialComplex ({a, b, c, d, e, f, a*b, b*c, c*d, d*e, e*f, f*a})

potentialPLs = apply(mats, i -> (i,M,N))
apply(potentialPLs, i -> isPolyptychPair i)
-- no true here
