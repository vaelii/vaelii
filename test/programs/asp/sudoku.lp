% A 9x9 sudoku with 26 givens and one solution: the twin of sudoku.vae.
sudokuGiven(1,2,6).
sudokuGiven(1,4,1).
sudokuGiven(1,5,8).
sudokuGiven(2,1,2).
sudokuGiven(2,5,4).
sudokuGiven(3,1,8).
sudokuGiven(3,3,1).
sudokuGiven(3,4,5).
sudokuGiven(3,6,7).
sudokuGiven(3,7,6).
sudokuGiven(4,4,7).
sudokuGiven(4,6,8).
sudokuGiven(4,9,6).
sudokuGiven(5,1,3).
sudokuGiven(5,2,2).
sudokuGiven(5,5,1).
sudokuGiven(5,9,7).
sudokuGiven(6,5,3).
sudokuGiven(7,1,7).
sudokuGiven(7,4,2).
sudokuGiven(7,6,5).
sudokuGiven(7,7,3).
sudokuGiven(7,8,9).
sudokuGiven(8,7,1).
sudokuGiven(8,9,8).
sudokuGiven(9,1,9).
board_index(1..9).
{cellValue(R,C,V)} :- board_index(R), board_index(C), board_index(V).
:- board_index(R), board_index(C), #count{V: cellValue(R,C,V)} != 1.
:- board_index(R), board_index(V), 2 #count{C: cellValue(R,C,V)}.
:- board_index(C), board_index(V), 2 #count{R: cellValue(R,C,V)}.
cellBox(R,C,(R-1)/3*3+(C-1)/3+1,(R-1)\3*3+(C-1)\3+1) :- board_index(R), board_index(C).
boxHolds(B,V,K) :- cellValue(R,C,V), cellBox(R,C,B,K).
:- board_index(B), board_index(V), 2 #count{K: boxHolds(B,V,K)}.
:- sudokuGiven(R,C,V), not cellValue(R,C,V).
#show cellValue/3.
