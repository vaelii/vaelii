% A knapsack of capacity 9: the twin of knapsack.vae.
packable_item(tent;lamp;stove;rope;map).
itemWeight(tent,5). itemWeight(lamp,3). itemWeight(stove,4). itemWeight(rope,2). itemWeight(map,1).
itemValue(tent,7). itemValue(lamp,4). itemValue(stove,5). itemValue(rope,3). itemValue(map,2).
{packed(I)} :- packable_item(I).
:- #sum{W,I: packed(I), itemWeight(I,W)} > 9.
left_behind(I) :- packable_item(I), not packed(I).
#minimize{V,I: left_behind(I), itemValue(I,V)}.
#show packed/1.
#show left_behind/1.
