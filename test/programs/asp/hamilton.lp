% Directed Hamiltonian cycles of the cube graph Q3: the twin of hamilton.vae.
graph_node(q0).
graph_node(q1).
graph_node(q2).
graph_node(q3).
graph_node(q4).
graph_node(q5).
graph_node(q6).
graph_node(q7).
graphEdge(q0,q1). graphEdge(q1,q0).
graphEdge(q0,q2). graphEdge(q2,q0).
graphEdge(q0,q4). graphEdge(q4,q0).
graphEdge(q1,q3). graphEdge(q3,q1).
graphEdge(q1,q5). graphEdge(q5,q1).
graphEdge(q2,q3). graphEdge(q3,q2).
graphEdge(q2,q6). graphEdge(q6,q2).
graphEdge(q3,q7). graphEdge(q7,q3).
graphEdge(q4,q5). graphEdge(q5,q4).
graphEdge(q4,q6). graphEdge(q6,q4).
graphEdge(q5,q7). graphEdge(q7,q5).
graphEdge(q6,q7). graphEdge(q7,q6).
{tourEdge(X,Y)} :- graphEdge(X,Y).
:- graph_node(X), 2 #count{Y: tourEdge(X,Y)}.
:- graph_node(Y), 2 #count{X: tourEdge(X,Y)}.
tourReaches(q0,Y) :- tourEdge(q0,Y).
tourReaches(q0,Y) :- tourReaches(q0,X), tourEdge(X,Y).
:- graph_node(Y), not tourReaches(q0,Y).
#show tourEdge/2.
#show tourReaches/2.
