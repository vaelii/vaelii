% Three-colouring the Petersen graph: the twin of colouring.vae.
#include "petersen.lp".
colour_name(red;green;blue).
{colourOf(N,K)} :- graph_node(N), colour_name(K).
:- graph_node(N), #count{K: colourOf(N,K)} != 1.
:- graphEdge(A,B), colourOf(A,K), colourOf(B,K).
#show colourOf/2.
