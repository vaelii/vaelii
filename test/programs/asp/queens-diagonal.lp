% Eight queens with projected diagonals: the twin of queens-diagonal.vae.
board_index(1..8).
{queenAt(R,C)} :- board_index(R), board_index(C).
:- board_index(R), #count{C: queenAt(R,C)} < 1.
:- board_index(R), 2 #count{C: queenAt(R,C)}.
:- board_index(C), 2 #count{R: queenAt(R,C)}.
onSumDiagonal(R+C,R) :- queenAt(R,C).
onDifferenceDiagonal(R-C,R) :- queenAt(R,C).
:- onSumDiagonal(D,_), 2 #count{R: onSumDiagonal(D,R)}.
:- onDifferenceDiagonal(D,_), 2 #count{R: onDifferenceDiagonal(D,R)}.
#show queenAt/2.
