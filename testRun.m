load "h1dr.m";

K<t> := PolynomialRing(GF(2));

F,V := computeH1dR(2,1,7,t^3);


f := Open("frobeniusMatrix.txt", "w");
v := Open("cartierMatrix.txt", "w");

rows := NumberOfRows(F);

for i in [1 .. rows] do
    for j in [1 .. rows] do
        Write(f, Sprint(F[i][j]));
        Write(v, Sprint(V[i][j]));
    end for;
end for;
