open util/ordering[Tick] as TickOrder

sig Addr { }
sig Data { }

sig Memory {
 addrs : set Addr,
 map : addrs -> one Data
}

sig MainMemory extends Memory { }

sig Cache extends Memory {
 dirty : set addrs
}

sig System {
 cache : Cache,
 main : MainMemory
}

pred Write [m, m' : Memory, d : Data, a : Addr] {
 m'.map = m.map ++ (a -> d)
}

pred SysWrite[s, s': System, d: Data, a: Addr] { 
 Write[s.cache, s'.cache, d, a]
 s'.cache.dirty = s.cache.dirty + a
 s'.main = s.main
}

pred SysFlush[s, s': System, x : set Addr] { 
 x in s.cache.addrs and
  s'.cache.map = s.cache.map - { x->Data } 
  s'.cache.dirty = s.cache.dirty - x 
  s'.main.map = s.main.map ++
    {a: x, d: Data | d = s.cache.map[a]} 
}

pred DirtyInv[s: System] {
 all a: s.cache.addrs - s.cache.dirty | 
	s.cache.map[a] = s.main.map[a]
}


sig Tick {
	system : System
}

fact {
	Init[TickOrder/first.system]
	all t: Tick-TickOrder/last {
		some x: set Addr |
		SysFlush[t.system, TickOrder/next[t].system, x] or 
		some a : Addr, d : Data | 
			SysWrite[t.system, TickOrder/next[t].system, d, a]
	}
}

pred Init [s: System]{
 no s.cache.dirty
 no s.cache.map
 no s.main.map
}

pred freshDir [s: System] {
	some a : Addr { all d : Data {
		! ((a -> d) in s.main.map) &&
		! ((a -> d) in s.cache.map)
		}
	}
}

assert DirtyInvAssertionAlloy { 
	DirtyInv[TickOrder/first.system] =>
     DirtyInv[TickOrder/last.system]
}

check DirtyInvAssertionAlloy for 4 but 5 Tick
check DirtyInvAssertionAlloy for 4 but 10 Tick
check DirtyInvAssertionAlloy for 4 but 15 Tick
check DirtyInvAssertionAlloy for 4 but 20 Tick
check DirtyInvAssertionAlloy for 4 but 25 Tick

check DirtyInvAssertionAlloy for 5 but 5 Tick
check DirtyInvAssertionAlloy for 5 but 10 Tick
check DirtyInvAssertionAlloy for 5 but 15 Tick
check DirtyInvAssertionAlloy for 5 but 20 Tick
check DirtyInvAssertionAlloy for 5 but 25 Tick

check DirtyInvAssertionAlloy for 6 but 5 Tick
check DirtyInvAssertionAlloy for 6 but 10 Tick
check DirtyInvAssertionAlloy for 6 but 15 Tick
check DirtyInvAssertionAlloy for 6 but 20 Tick
check DirtyInvAssertionAlloy for 6 but 25 Tick

assert FreshDirAssertion {
     Init[TickOrder/first.system] =>
        freshDir[TickOrder/last.system]
  }

--check FreshDirAssertion for 4 but 4 Addr, 5 Memory, 5 Cache, 5 MainMemory, 5 System, 5 Tick

check FreshDirAssertion for 4 but 5 Tick
check FreshDirAssertion for 4 but 15 Tick
check FreshDirAssertion for 4 but 25 Tick

check FreshDirAssertion for 5 but 5 Tick
check FreshDirAssertion for 5 but 15 Tick
check FreshDirAssertion for 5 but 25 Tick

check FreshDirAssertion for 6 but 5 Tick
check FreshDirAssertion for 6 but 15 Tick
check FreshDirAssertion for 6 but 25 Tick


assert CacheInMain {
  DirtyInv[TickOrder/first.system] =>
	( all t : Tick | no t.system.cache.dirty => t.system.cache.map in t.system.main.map)
}

check CacheInMain for 4 but 5 Tick
check CacheInMain for 4 but 10 Tick
check CacheInMain for 4 but 15 Tick
check CacheInMain for 4 but 20 Tick
check CacheInMain for 4 but 25 Tick

check CacheInMain for 5 but 5 Tick
check CacheInMain for 5 but 10 Tick
check CacheInMain for 5 but 15 Tick
check CacheInMain for 5 but 20 Tick
check CacheInMain for 5 but 25 Tick

check CacheInMain for 6 but 5 Tick
check CacheInMain for 6 but 10 Tick
check CacheInMain for 6 but 15 Tick
check CacheInMain for 6 but 20 Tick
check CacheInMain for 6 but 25 Tick

