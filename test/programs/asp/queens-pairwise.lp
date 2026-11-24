% Eight queens, generate and test: the twin of queens-pairwise.vae.
board_index(1..8).
{queenAt(R,C)} :- board_index(R), board_index(C).
:- board_index(R), #count{C: queenAt(R,C)} < 1.
:- board_index(R), 2 #count{C: queenAt(R,C)}.
:- board_index(C), 2 #count{R: queenAt(R,C)}.
:- queenAt(R1,C1), queenAt(R2,C2), R1 < R2, |R1-R2| = |C1-C2|.
#show queenAt/2.
