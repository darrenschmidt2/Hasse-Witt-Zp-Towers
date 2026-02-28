load "h1dr.m";

K<t> := PolynomialRing(GF(3));

F,V := computeH1dR(3,1,3,t^2);


f := Open("frobeniusMatrix.txt", "w");
v := Open("cartierMatrix.txt", "w");

rows := NumberOfRows(F);

for i in [1 .. rows] do
    for j in [1 .. rows] do
        Write(f, Sprint(F[i][j]));
        Write(v, Sprint(V[i][j]));
    end for;
end for;
