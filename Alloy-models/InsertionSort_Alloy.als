/**
Case study taken from Imperative Alloy
*/

open util/ordering[Time] as to


sig Time {}

sig Sequence { elts: seq Int -> Time}


pred sorted[elts: seq Int] {
	all i: elts.inds - elts.lastIdx | let i' = i + 1 | i.elts <= i'.elts}

/*
pred declarativeSort [s: Sequence, t1, t2: Time]{
	some s': Sequence |
		(sorted[s'.elts.t1] && s.elts.t1 =  s'.elts.t1) &&
	s.elts.t2 = s'.elts.t1
}
*/

one sig Cnt { cur: Int -> Time}


pred minIdx [s: seq Int, c, i: Int] {
	i >= c && no i': s.inds | i' >= c && i'.s < i.s
}


pred insertionStep [s: Sequence, t1, t2: Time]{
	some i: Int |
		minIdx[s.elts.t1, Cnt.cur.t1, i] &&
		Cnt.cur.t2 = Cnt.cur.t1 + 1 and
		s.elts.t2 = s.elts.t1 ++ ((Cnt.cur.t2) -> i.(s.elts.t1) ++ (i->Cnt.cur.t2.(s.elts.t1)))
}


pred insertionSort [s: Sequence] {
	Cnt.cur.to/first = 0 &&
	all t: Time-to/last | let t' = t.next | insertionStep[s,t,t']
	and Cnt.cur.to/last = s.elts.to/last.lastIdx	
}


assert sortWorks {
	all s: Sequence |
		 insertionSort[s] implies  sorted[s.elts.to/last]
}

one sig Temp{
	idx: Int -> Time,
	min: Int -> Time, 
	minIdx: Int -> Time
}

pred findMin[s: Sequence, t, t': Time]{
	Temp.idx.t' = Temp.idx.t + 1 and
	(Temp.idx.t.(s.elts.t) < Temp.min.t) => (Temp.min.t' = Temp.idx.t.(s.elts.t) and Temp.minIdx.t' = Temp.idx.t)
	else (Temp.min.t' = Temp.min.t and Temp.minIdx.t' = Temp.minIdx.t)
}


pred newInsertionStep [s: Sequence, t1, t2: Time] {
	Temp.idx.t1 = Cnt.cur.t1 and Temp.min.t1 = Cnt.cur.t1.(s.elts.t1) and  Temp.minIdx.t1 = Cnt.cur.t1 and
	all t: Time-to/last | let t' = t.next |
	(findMin[s,t,t'] and 
	Temp.idx.to/last = s.elts.to/last.lastIdx) and 
	Cnt.cur.t2 = Cnt.cur.t1 +1 and
	s.elts.t2 = s.elts.t1 ++ ((Temp.minIdx.to/last) -> Cnt.cur.to/last.(s.elts.to/last))
				++	(Cnt.cur.to/last -> Temp.minIdx.to/last.(s.elts.to/last))
}

run newInsertionStep

pred Init[s: Sequence]{
	Cnt.cur.to/first = 0 and
	Temp.idx.to/first = Cnt.cur.to/first and
	Temp.min.to/first = Cnt.cur.to/first.(s.elts.to/first) and
	Temp.min.to/first = Cnt.cur.to/first 
}


assert findMinWorks{
	all s: Sequence |
	(Temp.idx.to/first = Cnt.cur.to/first and
	Temp.min.to/first = Cnt.cur.to/first.(s.elts.to/first) and
	Temp.minIdx.to/first = Cnt.cur.to/first and
	all t: Time - to/last | let t' = t.next | some t2 : Time | t2 in t'.next and
	findMin[s,t,t'] and Temp.idx.t2 = s.elts.t2.lastIdx) =>
	minIdx[s.elts.to/last, Cnt.cur.to/last, Temp.minIdx.to/last]
}


check sortWorks for 4 Sequence, 5 Time
check sortWorks for 4 Sequence, 10 Time
check sortWorks for 4 Sequence, 15 Time
check sortWorks for 4 Sequence, 20 Time
check sortWorks for 4 Sequence, 25 Time
check sortWorks for 4 Sequence, 30 Time
check sortWorks for 4 Sequence, 40 Time
check sortWorks for 4 Sequence, 50 Time
check sortWorks for 4 Sequence, 75 Time
check sortWorks for 4 Sequence, 100 Time

check sortWorks for 5 Sequence, 5 Time
check sortWorks for 5 Sequence, 10 Time
check sortWorks for 5 Sequence, 15 Time
check sortWorks for 5 Sequence, 20 Time
check sortWorks for 5 Sequence, 25 Time
check sortWorks for 5 Sequence, 30 Time
check sortWorks for 5 Sequence, 40 Time
check sortWorks for 5 Sequence, 50 Time
check sortWorks for 5 Sequence, 75 Time
check sortWorks for 5 Sequence, 100 Time

check sortWorks for 6 Sequence, 5 Time
check sortWorks for 6 Sequence, 10 Time
check sortWorks for 6 Sequence, 15 Time
check sortWorks for 6 Sequence, 20 Time
check sortWorks for 6 Sequence, 25 Time
check sortWorks for 6 Sequence, 30 Time
check sortWorks for 6 Sequence, 40 Time
check sortWorks for 6 Sequence, 50 Time
check sortWorks for 6 Sequence, 75 Time
check sortWorks for 6 Sequence, 100 Time


check findMinWorks for 4 Sequence, 5 Time
check findMinWorks for 4 Sequence, 10 Time
check findMinWorks for 4 Sequence, 15 Time
check findMinWorks for 4 Sequence, 20 Time
check findMinWorks for 4 Sequence, 25 Time
check findMinWorks for 4 Sequence, 30 Time
check findMinWorks for 4 Sequence, 40 Time
check findMinWorks for 4 Sequence, 50 Time
check findMinWorks for 4 Sequence, 75 Time
check findMinWorks for 4 Sequence, 100 Time

check findMinWorks for 5 Sequence, 5 Time
check findMinWorks for 5 Sequence, 10 Time
check findMinWorks for 5 Sequence, 15 Time
check findMinWorks for 5 Sequence, 20 Time
check findMinWorks for 5 Sequence, 25 Time
check findMinWorks for 5 Sequence, 30 Time
check findMinWorks for 5 Sequence, 40 Time
check findMinWorks for 5 Sequence, 50 Time
check findMinWorks for 5 Sequence, 75 Time
check findMinWorks for 5 Sequence, 100 Time

check findMinWorks for 6 Sequence, 5 Time
check findMinWorks for 6 Sequence, 10 Time
check findMinWorks for 6 Sequence, 15 Time
check findMinWorks for 6 Sequence, 20 Time
check findMinWorks for 6 Sequence, 25 Time
check findMinWorks for 6 Sequence, 30 Time
check findMinWorks for 6 Sequence, 40 Time
check findMinWorks for 6 Sequence, 50 Time
check findMinWorks for 6 Sequence, 75 Time
check findMinWorks for 6 Sequence, 100 Time
