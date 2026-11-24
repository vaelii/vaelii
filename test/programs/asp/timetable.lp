% Five talks in three slots, two objective levels: the twin of timetable.vae.
conference_talk(talkA;talkB;talkC;talkD;talkE).
time_slot(morning;noon;evening).
talkClash(talkA,talkB). talkClash(talkC,talkD). talkClash(talkB,talkE).
slotAvoided(talkA,morning). slotAvoided(talkA,noon). slotAvoided(talkB,morning).
slotAvoided(talkB,noon). slotAvoided(talkC,evening). slotAvoided(talkD,noon).
slotAvoided(talkD,evening). slotAvoided(talkE,noon). slotAvoided(talkE,evening).
{scheduledAt(T,S)} :- conference_talk(T), time_slot(S).
:- conference_talk(T), #count{S: scheduledAt(T,S)} != 1.
:- time_slot(S), 3 #count{T: scheduledAt(T,S)}.
:- talkClash(A,B), scheduledAt(A,S), scheduledAt(B,S).
:~ slotAvoided(T,S), scheduledAt(T,S). [1@2,T,S]
:~ time_slot(S), 2 #count{T: scheduledAt(T,S)}. [1@1,S]
#show scheduledAt/2.
