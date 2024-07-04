module family
open util/ordering [Time] as T

sig Time {}

abstract sig Person {
    children, parents, siblings: set Person -> Time,
    spouse: lone Person -> Time,
    alive: set Time
} 

sig Man, Woman extends Person {}

// ---------------- Predicate ----------------

// Two persons are blood relatives at time t iff they have a common ancestor at time t
pred BloodRelatives [p, q: Person, t: Time] {
    some p.*(parents.t) & q.*(parents.t)
}

// ---------------- Fact ----------------

// Define inverse relationship between parents and children
fact {
    all t: Time | parents.t = ~(children.t)
}

// Define siblings as those with the same parents excluding oneself
fact {
    all t: Time | all p: Person | 
        p.siblings.t = (p.parents.t).children.t - p
}

// Static constraints and symmetric spouse relationships
fact {
    all t: Time {
        no p: Person | p in p.^(parents.t)
        all p: Person | 
            lone (p.parents.t & Man),
            lone (p.parents.t & Woman),
            (p in Man => p.spouse.t in Woman),
            (p in Woman => p.spouse.t in Man),
            no p | one p.spouse.t and (p.spouse.t in p.siblings.t or BloodRelatives [p, p.spouse.t, t]),
            no (p.children.t & q.children.t & p != q) => not BloodRelatives [p, q, t]
        spouse.t =  ~(spouse.t)
        all p: Person | not p.alive.t => (no p.children.t, no p.spouse.t)
    }
}

// ------------------------ Dynamic model ------------------------

// Simplified frame condition predicate for changes
pred noChangeExcept [ps: set Person, t, t': Time] {
    all p: Person - ps | p.children.t' = p.children, p.spouse.t' = p.spouse, p.alive.t' = p.alive
}

// Life events
pred marriage [m: Man, w: Woman, t, t': Time] {
    m+w in alive.t, no (m+w).spouse.t
    m.spouse.t' = w, w.spouse.t' = m
    noChangeExcept [m+w, t, t']
}

pred birth [t, t': Time] {
    one p: Person | p !in alive.t, alive.t' = alive.t + p
    noChangeExcept [none, t, t']
}

pred birthFromParents [m: Man, w: Woman, t, t': Time] {
    m+w in alive.t, m.spouse.t = w
    one p: Person | p !in alive.t, alive.t' = alive.t + p, m.children.t' += p, w.children.t' += p
    noChangeExcept [m+w, t, t']
}

// Initial state condition
pred init [t: Time] {
    no children.t, no spouse.t, no alive.t
}

// System evolution trace
pred Trace {
    init[T/first]  // Initialize at the first time
    all t: Time - T/last | let t' = T/next[t] |  // For each time until the last
        birth[t, t'], marriage[t, t'],birthFromParents[t, t']
}

run Trace for 5 but 8 Time, 4 Man, 4 Woman

// ------------------- Predicate for finding instances -------------------

pred marriageInstance {
    some t: Time |  // At some time
    some m: Man, w: Woman |  // For some man and woman
    let t' = T/next[t] |  // At the next time point
    marriage[m, w, t, t']  // A marriage occurs
}
run marriageInstance for 5
