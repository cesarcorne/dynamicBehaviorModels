/**
Case study taken from Imperative Alloy
*/

open util/ordering[Time] as to

sig Time {}

sig Name {}

abstract sig Path {}

sig NonEmptyPath extends Path { first: Name, rest: Path }

sig EmptyPath extends Path {}

abstract sig INode {}

sig DirNode extends INode { files: Name ->INode }

one sig RootNode extends DirNode {}

sig FileNode extends INode { data: Data ->Time }

sig Data {}

one sig MVar { 
	path: Path ->Time, 
	current: INode ->Time, 
	mdata: Data ->Time
}


pred navigate[t,t' : Time]{
	MVar.path.t' = MVar.path.t.rest and
	MVar.current.t' = (MVar.path.t.first).(MVar.current.t.files) and
	MVar.mdata.t' = MVar.mdata.t
}


pred read []{
	all t : Time-last | let t' = t.next | 
		navigate[t,t'] and MVar.current.t' in FileNode and
	MVar.mdata.t' = MVar.current.t.data.t and
	MVar.path.t' = MVar.path.t and
	MVar.current.t' = MVar.current.t
}


pred write []{
	all t : Time-last | let t' = t.next |
		navigate[t,t'] and MVar.current.t' in FileNode and
	let file = MVar.current.t |
		file.data.t = MVar.mdata.t' 
}


one sig Temp { tdata: Data -> Time }


assert readMatchesPriorWrite{
	all t: Time - to/last | let t' = t.next |
	(MVar.current.to/first = RootNode &&
	no f: FileNode | f.data.to/first = MVar.mdata.to/first) &&
	write[] and
	Temp.tdata.t' = MVar.mdata.t' and
	read[] implies Temp.tdata.to/last = MVar.mdata.to/last
}

check readMatchesPriorWrite for 4 but 5 Time
check readMatchesPriorWrite for 4 but 10 Time
check readMatchesPriorWrite for 4 but 15 Time
check readMatchesPriorWrite for 4 but 20 Time
check readMatchesPriorWrite for 4 but 25 Time
check readMatchesPriorWrite for 4 but 30 Time
check readMatchesPriorWrite for 4 but 40 Time
check readMatchesPriorWrite for 4 but 50 Time

check readMatchesPriorWrite for 6 but 5 Time
check readMatchesPriorWrite for 6 but 10 Time
check readMatchesPriorWrite for 6 but 15 Time
check readMatchesPriorWrite for 6 but 20 Time
check readMatchesPriorWrite for 6 but 25 Time
check readMatchesPriorWrite for 6 but 30 Time
check readMatchesPriorWrite for 6 but 40 Time
check readMatchesPriorWrite for 6 but 50 Time

check readMatchesPriorWrite for 8 but 5 Time
check readMatchesPriorWrite for 8 but 10 Time
check readMatchesPriorWrite for 8 but 15 Time
check readMatchesPriorWrite for 8 but 20 Time
check readMatchesPriorWrite for 8 but 25 Time
check readMatchesPriorWrite for 8 but 30 Time
check readMatchesPriorWrite for 8 but 40 Time
check readMatchesPriorWrite for 8 but 50 Time
