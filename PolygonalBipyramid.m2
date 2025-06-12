needsPackage "SimplicialComplexes"

PolygonalBipyramidComplex = method()

PolygonalBipyramidComplex(PolynomialRing) := (R) -> (
    polygonFaces := append(for i from 2 to numgens(R)-2 list(
        (gens R)#i * (gens R)#(i+1)
        ), (gens R)#2*(gens R)#(numgens(R)-1));
    topFaces := for i from 2 to numgens(R)-1 list(
        (gens R)#i * (gens R)#0
        );
    bottomFaces := for i from 2 to numgens(R)-1 list(
        (gens R)#i * (gens R)#1
        );
    fcs := join(polygonFaces, join(topFaces,bottomFaces));
    simplicialComplex(fcs)
)

end--
restart
load "PolygonalBipyramid.m2"

--Test--

R = ZZ[a..r]
PolygonalBipyramidComplex(R)
