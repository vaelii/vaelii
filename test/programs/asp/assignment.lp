% Assigning three workers to three tasks at least total cost: the twin of assignment.vae.
worker(ann;bob;cal).
work_task(t1;t2;t3).
taskCost(ann,t1,4). taskCost(ann,t2,2). taskCost(ann,t3,8).
taskCost(bob,t1,4). taskCost(bob,t2,3). taskCost(bob,t3,7).
taskCost(cal,t1,3). taskCost(cal,t2,1). taskCost(cal,t3,6).
{assignedTo(P,T)} :- worker(P), work_task(T).
:- work_task(T), #count{P: assignedTo(P,T)} != 1.
:- worker(P), 2 #count{T: assignedTo(P,T)}.
#minimize{W,P,T: assignedTo(P,T), taskCost(P,T,W)}.
#show assignedTo/2.
