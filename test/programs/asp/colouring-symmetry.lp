% Three-colouring the Petersen graph, colour symmetry broken: the twin of
% colouring-symmetry.vae.
#include "petersen.lp".
colour_name(red;green;blue).
{colourOf(N,K)} :- graph_node(N), colour_name(K).
:- graph_node(N), #count{K: colourOf(N,K)} != 1.
:- graphEdge(A,B), colourOf(A,K), colourOf(B,K).
:- not colourOf(p0,red).
:- not colourOf(p1,green).
#show colourOf/2.
