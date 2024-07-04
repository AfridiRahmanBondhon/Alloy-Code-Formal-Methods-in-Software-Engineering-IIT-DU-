module examples/hotel
open util/ordering [Key] as KO

sig Key {}

sig Room {
  keys: set Key,
  currentKey: Key
}

sig Guest {
  gkeys: set Key
}

one sig FrontDesk {
  lastKey: Room -> lone Key,
  occupant: Room -> Guest
}

fact KeyUniqueness {
  all k: Key | lone keys.k
  always all r: Room | r.currentKey in r.keys 
}

fun nextKey[k: Key, ks: set Key]: set Key {
  KO/min [KO/nexts[k] & ks]
}

pred init {
  no Guest.gkeys
  no FrontDesk.occupant
  all r: Room | r.(FrontDesk.lastKey) = r.currentKey
}

pred entry[g: Guest, r: Room, k: Key] {
  k in g.gkeys
  let ck = r.currentKey |
    (k = ck and ck' = ck) or
    (k = nextKey[ck, r.keys] and ck' = k)
}

pred checkin[g: Guest, r: Room, k: Key] {
  g.gkeys' = g.gkeys + k
  no r.(FrontDesk.occupant)
  r.(FrontDesk.occupant)' = r -> g
  r.(FrontDesk.lastKey)' = r -> k
}

pred checkout[g: Guest] {
  let occ = FrontDesk.occupant |
    some occ.g
    occ' = occ - (Room -> g)
}

fact Traces {
  init
  always {
    some g: Guest, r: Room, k: Key |
      entry[g, r, k] or checkin[g, r, k] or checkout[g]
  }
}

assert NoBadEntry {
  always all r: Room, g: Guest, k: Key | 
    (entry[g, r, k] and some r.(FrontDesk.occupant)) implies g in r.(FrontDesk.occupant)
}

check NoBadEntry for 3 but 2 Room, 2 Guest, 20 Time
